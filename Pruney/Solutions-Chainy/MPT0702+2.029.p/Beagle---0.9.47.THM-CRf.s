%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 463 expanded)
%              Number of leaves         :   28 ( 181 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 (1081 expanded)
%              Number of equality atoms :   35 ( 201 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k6_subset_1(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16)) = k9_relat_1(C_17,k6_subset_1(A_15,B_16))
      | ~ v2_funct_1(C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1125,plain,(
    ! [C_88,A_89,B_90] :
      ( k4_xboole_0(k9_relat_1(C_88,A_89),k9_relat_1(C_88,B_90)) = k9_relat_1(C_88,k4_xboole_0(A_89,B_90))
      | ~ v2_funct_1(C_88)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_34,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_144,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_1146,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_144])).

tff(c_1174,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1146])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,k9_relat_1(B_21,A_20)),A_20)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1192,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_26])).

tff(c_1202,plain,(
    r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1192])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_53,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_299,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(k2_xboole_0(A_46,B_48),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_323,plain,(
    ! [A_49,B_50] : r1_tarski(A_49,k2_xboole_0(A_49,B_50)) ),
    inference(resolution,[status(thm)],[c_6,c_299])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_420,plain,(
    ! [A_53,B_54,B_55] : r1_tarski(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) ),
    inference(resolution,[status(thm)],[c_323,c_12])).

tff(c_513,plain,(
    ! [A_60,B_61,B_62] : r1_tarski(k4_xboole_0(A_60,B_61),k2_xboole_0(A_60,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_420])).

tff(c_542,plain,(
    ! [B_61] : r1_tarski(k4_xboole_0('#skF_1',B_61),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_513])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,k10_relat_1(B_19,k9_relat_1(B_19,A_18)))
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1189,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_24])).

tff(c_1200,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_542,c_1189])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1239,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1200,c_2])).

tff(c_1248,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k10_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_1239])).

tff(c_115,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_115,c_28])).

tff(c_1254,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_123])).

tff(c_563,plain,(
    ! [B_63] : r1_tarski(k4_xboole_0('#skF_1',B_63),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_513])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_581,plain,(
    ! [B_63] : k4_xboole_0(k4_xboole_0('#skF_1',B_63),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_563,c_10])).

tff(c_1265,plain,(
    k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_581])).

tff(c_234,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1744,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(A_102,B_103) = A_102
      | ~ r1_tarski(A_102,k4_xboole_0(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_18,c_234])).

tff(c_1747,plain,
    ( k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),k1_relat_1('#skF_3')) = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_1744])).

tff(c_1796,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_1747])).

tff(c_1797,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1254,c_1796])).

tff(c_451,plain,(
    ! [A_53,B_54,B_55] : k4_xboole_0(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_420,c_10])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_39,plain,(
    ! [C_17,A_15,B_16] :
      ( k4_xboole_0(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16)) = k9_relat_1(C_17,k4_xboole_0(A_15,B_16))
      | ~ v2_funct_1(C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_1183,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_16)) = k4_xboole_0(k1_xboole_0,k9_relat_1('#skF_3',B_16))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_39])).

tff(c_1196,plain,(
    ! [B_16] : k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_16)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_147,c_1183])).

tff(c_1679,plain,(
    ! [B_101] : k9_relat_1('#skF_3',k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),B_101)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1196])).

tff(c_1702,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_1679])).

tff(c_1731,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_26])).

tff(c_1741,plain,(
    r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1731])).

tff(c_1874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1797,c_1741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.67  
% 3.51/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.67  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.51/1.67  
% 3.51/1.67  %Foreground sorts:
% 3.51/1.67  
% 3.51/1.67  
% 3.51/1.67  %Background operators:
% 3.51/1.67  
% 3.51/1.67  
% 3.51/1.67  %Foreground operators:
% 3.51/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.51/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.51/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.51/1.67  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.51/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.51/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.51/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.67  
% 3.90/1.69  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 3.90/1.69  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.90/1.69  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 3.90/1.69  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.90/1.69  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 3.90/1.69  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.90/1.69  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.90/1.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.90/1.69  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.90/1.69  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.90/1.69  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.90/1.69  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.90/1.69  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.90/1.69  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.90/1.69  tff(c_20, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.90/1.69  tff(c_22, plain, (![C_17, A_15, B_16]: (k6_subset_1(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16))=k9_relat_1(C_17, k6_subset_1(A_15, B_16)) | ~v2_funct_1(C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.90/1.69  tff(c_1125, plain, (![C_88, A_89, B_90]: (k4_xboole_0(k9_relat_1(C_88, A_89), k9_relat_1(C_88, B_90))=k9_relat_1(C_88, k4_xboole_0(A_89, B_90)) | ~v2_funct_1(C_88) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.90/1.69  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.90/1.69  tff(c_124, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.69  tff(c_144, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_124])).
% 3.90/1.69  tff(c_1146, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1125, c_144])).
% 3.90/1.69  tff(c_1174, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1146])).
% 3.90/1.69  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, k9_relat_1(B_21, A_20)), A_20) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.69  tff(c_1192, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1174, c_26])).
% 3.90/1.69  tff(c_1202, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1192])).
% 3.90/1.69  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.90/1.69  tff(c_53, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.90/1.69  tff(c_71, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_53])).
% 3.90/1.69  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.90/1.69  tff(c_70, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_18, c_53])).
% 3.90/1.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.69  tff(c_299, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(k2_xboole_0(A_46, B_48), C_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.69  tff(c_323, plain, (![A_49, B_50]: (r1_tarski(A_49, k2_xboole_0(A_49, B_50)))), inference(resolution, [status(thm)], [c_6, c_299])).
% 3.90/1.69  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.69  tff(c_420, plain, (![A_53, B_54, B_55]: (r1_tarski(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55)))), inference(resolution, [status(thm)], [c_323, c_12])).
% 3.90/1.69  tff(c_513, plain, (![A_60, B_61, B_62]: (r1_tarski(k4_xboole_0(A_60, B_61), k2_xboole_0(A_60, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_420])).
% 3.90/1.69  tff(c_542, plain, (![B_61]: (r1_tarski(k4_xboole_0('#skF_1', B_61), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_513])).
% 3.90/1.69  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(A_18, k10_relat_1(B_19, k9_relat_1(B_19, A_18))) | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.90/1.69  tff(c_1189, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0)) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1174, c_24])).
% 3.90/1.69  tff(c_1200, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_542, c_1189])).
% 3.90/1.69  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.69  tff(c_1239, plain, (k4_xboole_0('#skF_1', '#skF_2')=k10_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1200, c_2])).
% 3.90/1.69  tff(c_1248, plain, (k4_xboole_0('#skF_1', '#skF_2')=k10_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_1239])).
% 3.90/1.69  tff(c_115, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.69  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.90/1.69  tff(c_123, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_115, c_28])).
% 3.90/1.69  tff(c_1254, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_123])).
% 3.90/1.69  tff(c_563, plain, (![B_63]: (r1_tarski(k4_xboole_0('#skF_1', B_63), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_513])).
% 3.90/1.69  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.69  tff(c_581, plain, (![B_63]: (k4_xboole_0(k4_xboole_0('#skF_1', B_63), k1_relat_1('#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_563, c_10])).
% 3.90/1.69  tff(c_1265, plain, (k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), k1_relat_1('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1248, c_581])).
% 3.90/1.69  tff(c_234, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.69  tff(c_1744, plain, (![A_102, B_103]: (k4_xboole_0(A_102, B_103)=A_102 | ~r1_tarski(A_102, k4_xboole_0(A_102, B_103)))), inference(resolution, [status(thm)], [c_18, c_234])).
% 3.90/1.69  tff(c_1747, plain, (k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), k1_relat_1('#skF_3'))=k10_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1265, c_1744])).
% 3.90/1.69  tff(c_1796, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_1747])).
% 3.90/1.69  tff(c_1797, plain, (~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1254, c_1796])).
% 3.90/1.69  tff(c_451, plain, (![A_53, B_54, B_55]: (k4_xboole_0(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55))=k1_xboole_0)), inference(resolution, [status(thm)], [c_420, c_10])).
% 3.90/1.69  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.90/1.69  tff(c_147, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_124])).
% 3.90/1.69  tff(c_39, plain, (![C_17, A_15, B_16]: (k4_xboole_0(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16))=k9_relat_1(C_17, k4_xboole_0(A_15, B_16)) | ~v2_funct_1(C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.90/1.69  tff(c_1183, plain, (![B_16]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_16))=k4_xboole_0(k1_xboole_0, k9_relat_1('#skF_3', B_16)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_39])).
% 3.90/1.69  tff(c_1196, plain, (![B_16]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_16))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_147, c_1183])).
% 3.90/1.69  tff(c_1679, plain, (![B_101]: (k9_relat_1('#skF_3', k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), B_101))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1196])).
% 3.90/1.69  tff(c_1702, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_451, c_1679])).
% 3.90/1.69  tff(c_1731, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1702, c_26])).
% 3.90/1.69  tff(c_1741, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1731])).
% 3.90/1.69  tff(c_1874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1797, c_1741])).
% 3.90/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.69  
% 3.90/1.69  Inference rules
% 3.90/1.69  ----------------------
% 3.90/1.69  #Ref     : 0
% 3.90/1.69  #Sup     : 447
% 3.90/1.69  #Fact    : 0
% 3.90/1.69  #Define  : 0
% 3.90/1.69  #Split   : 2
% 3.90/1.69  #Chain   : 0
% 3.90/1.69  #Close   : 0
% 3.90/1.69  
% 3.90/1.69  Ordering : KBO
% 3.90/1.69  
% 3.90/1.69  Simplification rules
% 3.90/1.69  ----------------------
% 3.90/1.69  #Subsume      : 17
% 3.90/1.69  #Demod        : 311
% 3.90/1.69  #Tautology    : 267
% 3.90/1.69  #SimpNegUnit  : 3
% 3.90/1.69  #BackRed      : 4
% 3.90/1.69  
% 3.90/1.69  #Partial instantiations: 0
% 3.90/1.69  #Strategies tried      : 1
% 3.90/1.69  
% 3.90/1.69  Timing (in seconds)
% 3.90/1.69  ----------------------
% 3.90/1.69  Preprocessing        : 0.33
% 3.90/1.69  Parsing              : 0.18
% 3.90/1.69  CNF conversion       : 0.02
% 3.90/1.69  Main loop            : 0.55
% 3.90/1.69  Inferencing          : 0.19
% 3.90/1.69  Reduction            : 0.20
% 3.90/1.69  Demodulation         : 0.15
% 3.90/1.69  BG Simplification    : 0.02
% 3.90/1.69  Subsumption          : 0.10
% 3.90/1.69  Abstraction          : 0.03
% 3.90/1.69  MUC search           : 0.00
% 3.90/1.69  Cooper               : 0.00
% 3.90/1.70  Total                : 0.92
% 3.90/1.70  Index Insertion      : 0.00
% 3.90/1.70  Index Deletion       : 0.00
% 3.90/1.70  Index Matching       : 0.00
% 3.90/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
