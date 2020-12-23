%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 103 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 187 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_90,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_312,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | k4_xboole_0(A_51,B_52) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_329,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_312,c_32])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [B_44] : k4_xboole_0(B_44,B_44) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [B_44] : r1_tarski(k1_xboole_0,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_16])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_81,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_99,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_330,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(k2_xboole_0(A_53,B_55),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_379,plain,(
    ! [A_57,B_58,B_59] : r1_tarski(A_57,k2_xboole_0(k2_xboole_0(A_57,B_58),B_59)) ),
    inference(resolution,[status(thm)],[c_22,c_330])).

tff(c_465,plain,(
    ! [A_62,B_63,B_64] : r1_tarski(k4_xboole_0(A_62,B_63),k2_xboole_0(A_62,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_379])).

tff(c_477,plain,(
    ! [B_63] : r1_tarski(k4_xboole_0('#skF_1',B_63),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_465])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_152,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_24,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1604,plain,(
    ! [C_106,A_107,B_108] :
      ( k4_xboole_0(k10_relat_1(C_106,A_107),k10_relat_1(C_106,B_108)) = k10_relat_1(C_106,k4_xboole_0(A_107,B_108))
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_1638,plain,(
    ! [C_106,B_108] :
      ( k10_relat_1(C_106,k4_xboole_0(B_108,B_108)) = k1_xboole_0
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_152])).

tff(c_1656,plain,(
    ! [C_109] :
      ( k10_relat_1(C_109,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1638])).

tff(c_1659,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1656])).

tff(c_1662,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1659])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_149,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( k6_subset_1(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21)) = k9_relat_1(C_22,k6_subset_1(A_20,B_21))
      | ~ v2_funct_1(C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2064,plain,(
    ! [C_119,A_120,B_121] :
      ( k4_xboole_0(k9_relat_1(C_119,A_120),k9_relat_1(C_119,B_121)) = k9_relat_1(C_119,k4_xboole_0(A_120,B_121))
      | ~ v2_funct_1(C_119)
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_26])).

tff(c_2120,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2064])).

tff(c_2135,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_2120])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k10_relat_1(B_27,k9_relat_1(B_27,A_26)))
      | ~ r1_tarski(A_26,k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2335,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2135,c_30])).

tff(c_2343,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_477,c_1662,c_2335])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2376,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2343,c_2])).

tff(c_2389,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_2376])).

tff(c_2391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_2389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.56  
% 3.32/1.56  %Foreground sorts:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Background operators:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Foreground operators:
% 3.32/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.32/1.56  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.32/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.32/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.56  
% 3.32/1.58  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.32/1.58  tff(f_90, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.32/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.58  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.32/1.58  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.32/1.58  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.32/1.58  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.32/1.58  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.32/1.58  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 3.32/1.58  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.32/1.58  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.32/1.58  tff(c_312, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | k4_xboole_0(A_51, B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.58  tff(c_32, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_329, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_312, c_32])).
% 3.32/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.58  tff(c_132, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.58  tff(c_153, plain, (![B_44]: (k4_xboole_0(B_44, B_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_132])).
% 3.32/1.58  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.58  tff(c_164, plain, (![B_44]: (r1_tarski(k1_xboole_0, B_44))), inference(superposition, [status(thm), theory('equality')], [c_153, c_16])).
% 3.32/1.58  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_36, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_81, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.58  tff(c_100, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_81])).
% 3.32/1.58  tff(c_99, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_16, c_81])).
% 3.32/1.58  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.58  tff(c_330, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(k2_xboole_0(A_53, B_55), C_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.58  tff(c_379, plain, (![A_57, B_58, B_59]: (r1_tarski(A_57, k2_xboole_0(k2_xboole_0(A_57, B_58), B_59)))), inference(resolution, [status(thm)], [c_22, c_330])).
% 3.32/1.58  tff(c_465, plain, (![A_62, B_63, B_64]: (r1_tarski(k4_xboole_0(A_62, B_63), k2_xboole_0(A_62, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_379])).
% 3.32/1.58  tff(c_477, plain, (![B_63]: (r1_tarski(k4_xboole_0('#skF_1', B_63), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_100, c_465])).
% 3.32/1.58  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_152, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_132])).
% 3.32/1.58  tff(c_24, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.32/1.58  tff(c_28, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.32/1.58  tff(c_1604, plain, (![C_106, A_107, B_108]: (k4_xboole_0(k10_relat_1(C_106, A_107), k10_relat_1(C_106, B_108))=k10_relat_1(C_106, k4_xboole_0(A_107, B_108)) | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 3.32/1.58  tff(c_1638, plain, (![C_106, B_108]: (k10_relat_1(C_106, k4_xboole_0(B_108, B_108))=k1_xboole_0 | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_152])).
% 3.32/1.58  tff(c_1656, plain, (![C_109]: (k10_relat_1(C_109, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_109) | ~v1_relat_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1638])).
% 3.32/1.58  tff(c_1659, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1656])).
% 3.32/1.58  tff(c_1662, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1659])).
% 3.32/1.58  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.58  tff(c_149, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_132])).
% 3.32/1.58  tff(c_26, plain, (![C_22, A_20, B_21]: (k6_subset_1(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21))=k9_relat_1(C_22, k6_subset_1(A_20, B_21)) | ~v2_funct_1(C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.32/1.58  tff(c_2064, plain, (![C_119, A_120, B_121]: (k4_xboole_0(k9_relat_1(C_119, A_120), k9_relat_1(C_119, B_121))=k9_relat_1(C_119, k4_xboole_0(A_120, B_121)) | ~v2_funct_1(C_119) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_26])).
% 3.32/1.58  tff(c_2120, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_149, c_2064])).
% 3.32/1.58  tff(c_2135, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_2120])).
% 3.32/1.58  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(A_26, k10_relat_1(B_27, k9_relat_1(B_27, A_26))) | ~r1_tarski(A_26, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.58  tff(c_2335, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0)) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2135, c_30])).
% 3.32/1.58  tff(c_2343, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_477, c_1662, c_2335])).
% 3.32/1.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.58  tff(c_2376, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2343, c_2])).
% 3.32/1.58  tff(c_2389, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_164, c_2376])).
% 3.32/1.58  tff(c_2391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_2389])).
% 3.32/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  Inference rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Ref     : 0
% 3.32/1.58  #Sup     : 560
% 3.32/1.58  #Fact    : 0
% 3.32/1.58  #Define  : 0
% 3.32/1.58  #Split   : 2
% 3.32/1.58  #Chain   : 0
% 3.32/1.58  #Close   : 0
% 3.32/1.58  
% 3.32/1.58  Ordering : KBO
% 3.32/1.58  
% 3.32/1.58  Simplification rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Subsume      : 9
% 3.32/1.58  #Demod        : 461
% 3.32/1.58  #Tautology    : 401
% 3.32/1.58  #SimpNegUnit  : 1
% 3.32/1.58  #BackRed      : 4
% 3.32/1.58  
% 3.32/1.58  #Partial instantiations: 0
% 3.32/1.58  #Strategies tried      : 1
% 3.32/1.58  
% 3.32/1.58  Timing (in seconds)
% 3.32/1.58  ----------------------
% 3.32/1.58  Preprocessing        : 0.29
% 3.32/1.58  Parsing              : 0.15
% 3.32/1.58  CNF conversion       : 0.02
% 3.32/1.58  Main loop            : 0.49
% 3.32/1.58  Inferencing          : 0.16
% 3.32/1.58  Reduction            : 0.19
% 3.32/1.58  Demodulation         : 0.15
% 3.32/1.58  BG Simplification    : 0.02
% 3.32/1.58  Subsumption          : 0.08
% 3.32/1.58  Abstraction          : 0.03
% 3.32/1.58  MUC search           : 0.00
% 3.32/1.58  Cooper               : 0.00
% 3.32/1.58  Total                : 0.81
% 3.32/1.58  Index Insertion      : 0.00
% 3.32/1.58  Index Deletion       : 0.00
% 3.32/1.58  Index Matching       : 0.00
% 3.32/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
