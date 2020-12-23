%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 118 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 229 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_120,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_128,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_30])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_469,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k4_xboole_0(A_63,B_64),C_65)
      | ~ r1_tarski(A_63,k2_xboole_0(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_1111,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,k2_xboole_0(B_93,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_469,c_215])).

tff(c_1159,plain,(
    ! [B_94] : k4_xboole_0(k2_xboole_0(B_94,k1_xboole_0),B_94) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1111])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_268,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_360,plain,(
    ! [A_57,A_58,B_59] :
      ( r1_tarski(A_57,A_58)
      | ~ r1_tarski(A_57,k4_xboole_0(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_16,c_268])).

tff(c_400,plain,(
    ! [A_3,A_58,B_59] :
      ( r1_tarski(A_3,A_58)
      | k4_xboole_0(A_3,k4_xboole_0(A_58,B_59)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_360])).

tff(c_1219,plain,(
    ! [A_58,B_59] : r1_tarski(k2_xboole_0(k4_xboole_0(A_58,B_59),k1_xboole_0),A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_400])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_310,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_53,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_268])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1896,plain,(
    ! [A_112,A_113] :
      ( r1_tarski(A_112,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_112,A_113)
      | ~ r1_tarski(A_113,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_310,c_12])).

tff(c_3717,plain,(
    ! [A_162,B_163] :
      ( r1_tarski(A_162,k1_relat_1('#skF_3'))
      | ~ r1_tarski(k2_xboole_0(A_162,B_163),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_1896])).

tff(c_3731,plain,(
    ! [B_59] : r1_tarski(k4_xboole_0('#skF_1',B_59),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1219,c_3717])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_57,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_22,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22] :
      ( k6_subset_1(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k6_subset_1(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1264,plain,(
    ! [C_95,A_96,B_97] :
      ( k4_xboole_0(k10_relat_1(C_95,A_96),k10_relat_1(C_95,B_97)) = k10_relat_1(C_95,k4_xboole_0(A_96,B_97))
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_26])).

tff(c_1292,plain,(
    ! [C_95,B_97] :
      ( k10_relat_1(C_95,k4_xboole_0(B_97,B_97)) = k1_xboole_0
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_81])).

tff(c_1387,plain,(
    ! [C_100] :
      ( k10_relat_1(C_100,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_100)
      | ~ v1_relat_1(C_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1292])).

tff(c_1390,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1387])).

tff(c_1393,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1390])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k6_subset_1(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19)) = k9_relat_1(C_20,k6_subset_1(A_18,B_19))
      | ~ v2_funct_1(C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1809,plain,(
    ! [C_109,A_110,B_111] :
      ( k4_xboole_0(k9_relat_1(C_109,A_110),k9_relat_1(C_109,B_111)) = k9_relat_1(C_109,k4_xboole_0(A_110,B_111))
      | ~ v2_funct_1(C_109)
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_24])).

tff(c_36,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_76,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_1845,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_76])).

tff(c_1870,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_1845])).

tff(c_801,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,k10_relat_1(B_78,k9_relat_1(B_78,A_77)))
      | ~ r1_tarski(A_77,k1_relat_1(B_78))
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4838,plain,(
    ! [A_191,B_192] :
      ( k4_xboole_0(A_191,k10_relat_1(B_192,k9_relat_1(B_192,A_191))) = k1_xboole_0
      | ~ r1_tarski(A_191,k1_relat_1(B_192))
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_801,c_10])).

tff(c_4998,plain,
    ( k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_4838])).

tff(c_5051,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3731,c_1393,c_4998])).

tff(c_220,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_237,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_5137,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5051,c_237])).

tff(c_5178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_5137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:18:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.92  
% 4.81/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.93  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.81/1.93  
% 4.81/1.93  %Foreground sorts:
% 4.81/1.93  
% 4.81/1.93  
% 4.81/1.93  %Background operators:
% 4.81/1.93  
% 4.81/1.93  
% 4.81/1.93  %Foreground operators:
% 4.81/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.81/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.81/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.81/1.93  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.81/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.81/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.93  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.81/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.81/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.81/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.81/1.93  
% 4.81/1.94  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.81/1.94  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.81/1.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.81/1.94  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.81/1.94  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.81/1.94  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.81/1.94  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.81/1.94  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.81/1.94  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.81/1.94  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 4.81/1.94  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 4.81/1.94  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.81/1.94  tff(c_120, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/1.94  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.94  tff(c_128, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_30])).
% 4.81/1.94  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.94  tff(c_469, plain, (![A_63, B_64, C_65]: (r1_tarski(k4_xboole_0(A_63, B_64), C_65) | ~r1_tarski(A_63, k2_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.81/1.94  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.94  tff(c_195, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.94  tff(c_215, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_195])).
% 4.81/1.94  tff(c_1111, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, k2_xboole_0(B_93, k1_xboole_0)))), inference(resolution, [status(thm)], [c_469, c_215])).
% 4.81/1.94  tff(c_1159, plain, (![B_94]: (k4_xboole_0(k2_xboole_0(B_94, k1_xboole_0), B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1111])).
% 4.81/1.94  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/1.94  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.81/1.94  tff(c_268, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.81/1.94  tff(c_360, plain, (![A_57, A_58, B_59]: (r1_tarski(A_57, A_58) | ~r1_tarski(A_57, k4_xboole_0(A_58, B_59)))), inference(resolution, [status(thm)], [c_16, c_268])).
% 4.81/1.94  tff(c_400, plain, (![A_3, A_58, B_59]: (r1_tarski(A_3, A_58) | k4_xboole_0(A_3, k4_xboole_0(A_58, B_59))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_360])).
% 4.81/1.94  tff(c_1219, plain, (![A_58, B_59]: (r1_tarski(k2_xboole_0(k4_xboole_0(A_58, B_59), k1_xboole_0), A_58))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_400])).
% 4.81/1.94  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/1.94  tff(c_34, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.94  tff(c_310, plain, (![A_53]: (r1_tarski(A_53, k1_relat_1('#skF_3')) | ~r1_tarski(A_53, '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_268])).
% 4.81/1.94  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.81/1.94  tff(c_1896, plain, (![A_112, A_113]: (r1_tarski(A_112, k1_relat_1('#skF_3')) | ~r1_tarski(A_112, A_113) | ~r1_tarski(A_113, '#skF_1'))), inference(resolution, [status(thm)], [c_310, c_12])).
% 4.81/1.94  tff(c_3717, plain, (![A_162, B_163]: (r1_tarski(A_162, k1_relat_1('#skF_3')) | ~r1_tarski(k2_xboole_0(A_162, B_163), '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_1896])).
% 4.81/1.94  tff(c_3731, plain, (![B_59]: (r1_tarski(k4_xboole_0('#skF_1', B_59), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_1219, c_3717])).
% 4.81/1.94  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.94  tff(c_57, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/1.94  tff(c_81, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_57])).
% 4.81/1.94  tff(c_22, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/1.94  tff(c_26, plain, (![C_23, A_21, B_22]: (k6_subset_1(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k6_subset_1(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.81/1.94  tff(c_1264, plain, (![C_95, A_96, B_97]: (k4_xboole_0(k10_relat_1(C_95, A_96), k10_relat_1(C_95, B_97))=k10_relat_1(C_95, k4_xboole_0(A_96, B_97)) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_26])).
% 4.81/1.94  tff(c_1292, plain, (![C_95, B_97]: (k10_relat_1(C_95, k4_xboole_0(B_97, B_97))=k1_xboole_0 | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_81])).
% 4.81/1.94  tff(c_1387, plain, (![C_100]: (k10_relat_1(C_100, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_100) | ~v1_relat_1(C_100))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1292])).
% 4.81/1.94  tff(c_1390, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1387])).
% 4.81/1.94  tff(c_1393, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1390])).
% 4.81/1.94  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.94  tff(c_24, plain, (![C_20, A_18, B_19]: (k6_subset_1(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19))=k9_relat_1(C_20, k6_subset_1(A_18, B_19)) | ~v2_funct_1(C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.81/1.94  tff(c_1809, plain, (![C_109, A_110, B_111]: (k4_xboole_0(k9_relat_1(C_109, A_110), k9_relat_1(C_109, B_111))=k9_relat_1(C_109, k4_xboole_0(A_110, B_111)) | ~v2_funct_1(C_109) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_24])).
% 4.81/1.94  tff(c_36, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.94  tff(c_76, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_57])).
% 4.81/1.94  tff(c_1845, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1809, c_76])).
% 4.81/1.94  tff(c_1870, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_1845])).
% 4.81/1.94  tff(c_801, plain, (![A_77, B_78]: (r1_tarski(A_77, k10_relat_1(B_78, k9_relat_1(B_78, A_77))) | ~r1_tarski(A_77, k1_relat_1(B_78)) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.81/1.94  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/1.94  tff(c_4838, plain, (![A_191, B_192]: (k4_xboole_0(A_191, k10_relat_1(B_192, k9_relat_1(B_192, A_191)))=k1_xboole_0 | ~r1_tarski(A_191, k1_relat_1(B_192)) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_801, c_10])).
% 4.81/1.94  tff(c_4998, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1870, c_4838])).
% 4.81/1.94  tff(c_5051, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3731, c_1393, c_4998])).
% 4.81/1.94  tff(c_220, plain, (![A_46]: (k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_195])).
% 4.81/1.94  tff(c_237, plain, (![A_3]: (k1_xboole_0=A_3 | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_220])).
% 4.81/1.94  tff(c_5137, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5051, c_237])).
% 4.81/1.94  tff(c_5178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_5137])).
% 4.81/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.94  
% 4.81/1.94  Inference rules
% 4.81/1.94  ----------------------
% 4.81/1.94  #Ref     : 0
% 4.81/1.94  #Sup     : 1242
% 4.81/1.94  #Fact    : 0
% 4.81/1.94  #Define  : 0
% 4.81/1.94  #Split   : 3
% 4.81/1.94  #Chain   : 0
% 4.81/1.94  #Close   : 0
% 4.81/1.94  
% 4.81/1.94  Ordering : KBO
% 4.81/1.94  
% 4.81/1.94  Simplification rules
% 4.81/1.94  ----------------------
% 4.81/1.94  #Subsume      : 162
% 4.81/1.94  #Demod        : 1012
% 4.81/1.94  #Tautology    : 675
% 4.81/1.94  #SimpNegUnit  : 2
% 4.81/1.94  #BackRed      : 0
% 4.81/1.94  
% 4.81/1.94  #Partial instantiations: 0
% 4.81/1.94  #Strategies tried      : 1
% 4.81/1.94  
% 4.81/1.94  Timing (in seconds)
% 4.81/1.94  ----------------------
% 4.81/1.94  Preprocessing        : 0.30
% 4.81/1.94  Parsing              : 0.16
% 4.81/1.94  CNF conversion       : 0.02
% 4.81/1.94  Main loop            : 0.86
% 4.81/1.94  Inferencing          : 0.25
% 4.81/1.94  Reduction            : 0.33
% 4.81/1.94  Demodulation         : 0.25
% 4.81/1.94  BG Simplification    : 0.03
% 4.81/1.94  Subsumption          : 0.19
% 4.81/1.94  Abstraction          : 0.04
% 4.81/1.94  MUC search           : 0.00
% 4.81/1.94  Cooper               : 0.00
% 4.81/1.94  Total                : 1.19
% 4.81/1.94  Index Insertion      : 0.00
% 4.81/1.94  Index Deletion       : 0.00
% 4.81/1.94  Index Matching       : 0.00
% 4.81/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
