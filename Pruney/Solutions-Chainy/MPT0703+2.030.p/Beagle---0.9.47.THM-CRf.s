%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 9.69s
% Output     : CNFRefutation 9.80s
% Verified   : 
% Statistics : Number of formulae       :   63 (  71 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 119 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_40,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    k2_xboole_0(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) = k10_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_30,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_138,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(k2_xboole_0(A_53,B_55),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [A_53,B_55,B_29] : r1_tarski(A_53,k2_xboole_0(k2_xboole_0(A_53,B_55),B_29)) ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_746,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_tarski(k4_xboole_0(A_109,B_110),C_111)
      | ~ r1_tarski(A_109,k2_xboole_0(B_110,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6322,plain,(
    ! [A_256,B_257,B_258] :
      ( k4_xboole_0(A_256,B_257) = k1_xboole_0
      | ~ r1_tarski(A_256,k2_xboole_0(B_257,k4_xboole_0(B_258,k4_xboole_0(A_256,B_257)))) ) ),
    inference(resolution,[status(thm)],[c_746,c_20])).

tff(c_7176,plain,(
    ! [A_271,B_272] : k4_xboole_0(A_271,k2_xboole_0(A_271,B_272)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_6322])).

tff(c_7387,plain,(
    k4_xboole_0(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_7176])).

tff(c_32,plain,(
    ! [A_30,B_31] : k6_subset_1(A_30,B_31) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [C_36,A_34,B_35] :
      ( k6_subset_1(k10_relat_1(C_36,A_34),k10_relat_1(C_36,B_35)) = k10_relat_1(C_36,k6_subset_1(A_34,B_35))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_49,plain,(
    ! [C_36,A_34,B_35] :
      ( k4_xboole_0(k10_relat_1(C_36,A_34),k10_relat_1(C_36,B_35)) = k10_relat_1(C_36,k4_xboole_0(A_34,B_35))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_38])).

tff(c_8281,plain,
    ( k10_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7387,c_49])).

tff(c_8358,plain,(
    k10_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_8281])).

tff(c_42,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_447,plain,(
    ! [B_86,A_87] :
      ( r1_xboole_0(k2_relat_1(B_86),A_87)
      | k10_relat_1(B_86,A_87) != k1_xboole_0
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_xboole_0(A_22,C_24)
      | ~ r1_xboole_0(B_23,C_24)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5452,plain,(
    ! [A_244,A_245,B_246] :
      ( r1_xboole_0(A_244,A_245)
      | ~ r1_tarski(A_244,k2_relat_1(B_246))
      | k10_relat_1(B_246,A_245) != k1_xboole_0
      | ~ v1_relat_1(B_246) ) ),
    inference(resolution,[status(thm)],[c_447,c_26])).

tff(c_5484,plain,(
    ! [A_245] :
      ( r1_xboole_0('#skF_2',A_245)
      | k10_relat_1('#skF_4',A_245) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_5452])).

tff(c_5861,plain,(
    ! [A_249] :
      ( r1_xboole_0('#skF_2',A_249)
      | k10_relat_1('#skF_4',A_249) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5484])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_814,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(A_121,k2_xboole_0(B_122,C_123))
      | ~ r1_tarski(k4_xboole_0(A_121,B_122),C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1105,plain,(
    ! [A_132,B_133] : r1_tarski(A_132,k2_xboole_0(B_133,k4_xboole_0(A_132,B_133))) ),
    inference(resolution,[status(thm)],[c_6,c_814])).

tff(c_28,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_xboole_0(A_25,C_27)
      | ~ r1_tarski(A_25,k2_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1130,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(A_132,B_133)
      | ~ r1_xboole_0(A_132,k4_xboole_0(A_132,B_133)) ) ),
    inference(resolution,[status(thm)],[c_1105,c_28])).

tff(c_19437,plain,(
    ! [B_397] :
      ( r1_tarski('#skF_2',B_397)
      | k10_relat_1('#skF_4',k4_xboole_0('#skF_2',B_397)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5861,c_1130])).

tff(c_19477,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8358,c_19437])).

tff(c_19518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_19477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.69/3.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.75  
% 9.76/3.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.75  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 9.76/3.75  
% 9.76/3.75  %Foreground sorts:
% 9.76/3.75  
% 9.76/3.75  
% 9.76/3.75  %Background operators:
% 9.76/3.75  
% 9.76/3.75  
% 9.76/3.75  %Foreground operators:
% 9.76/3.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.76/3.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.76/3.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.76/3.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.76/3.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.76/3.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.76/3.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.76/3.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.76/3.75  tff('#skF_2', type, '#skF_2': $i).
% 9.76/3.75  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.76/3.75  tff('#skF_3', type, '#skF_3': $i).
% 9.76/3.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.76/3.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.76/3.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.76/3.75  tff('#skF_4', type, '#skF_4': $i).
% 9.76/3.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.76/3.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.76/3.75  
% 9.80/3.76  tff(f_105, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 9.80/3.76  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.80/3.76  tff(f_80, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.80/3.76  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.80/3.76  tff(f_62, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.80/3.76  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 9.80/3.76  tff(f_82, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.80/3.76  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 9.80/3.76  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 9.80/3.76  tff(f_72, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 9.80/3.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.80/3.76  tff(f_66, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.80/3.76  tff(f_78, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 9.80/3.76  tff(c_40, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.80/3.76  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.80/3.76  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.80/3.76  tff(c_44, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.80/3.76  tff(c_64, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.80/3.76  tff(c_80, plain, (k2_xboole_0(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))=k10_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_64])).
% 9.80/3.76  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.80/3.76  tff(c_138, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(k2_xboole_0(A_53, B_55), C_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.80/3.76  tff(c_156, plain, (![A_53, B_55, B_29]: (r1_tarski(A_53, k2_xboole_0(k2_xboole_0(A_53, B_55), B_29)))), inference(resolution, [status(thm)], [c_30, c_138])).
% 9.80/3.76  tff(c_746, plain, (![A_109, B_110, C_111]: (r1_tarski(k4_xboole_0(A_109, B_110), C_111) | ~r1_tarski(A_109, k2_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.80/3.76  tff(c_20, plain, (![A_14, B_15]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k4_xboole_0(B_15, A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.80/3.76  tff(c_6322, plain, (![A_256, B_257, B_258]: (k4_xboole_0(A_256, B_257)=k1_xboole_0 | ~r1_tarski(A_256, k2_xboole_0(B_257, k4_xboole_0(B_258, k4_xboole_0(A_256, B_257)))))), inference(resolution, [status(thm)], [c_746, c_20])).
% 9.80/3.76  tff(c_7176, plain, (![A_271, B_272]: (k4_xboole_0(A_271, k2_xboole_0(A_271, B_272))=k1_xboole_0)), inference(resolution, [status(thm)], [c_156, c_6322])).
% 9.80/3.76  tff(c_7387, plain, (k4_xboole_0(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_80, c_7176])).
% 9.80/3.76  tff(c_32, plain, (![A_30, B_31]: (k6_subset_1(A_30, B_31)=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.80/3.76  tff(c_38, plain, (![C_36, A_34, B_35]: (k6_subset_1(k10_relat_1(C_36, A_34), k10_relat_1(C_36, B_35))=k10_relat_1(C_36, k6_subset_1(A_34, B_35)) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.80/3.76  tff(c_49, plain, (![C_36, A_34, B_35]: (k4_xboole_0(k10_relat_1(C_36, A_34), k10_relat_1(C_36, B_35))=k10_relat_1(C_36, k4_xboole_0(A_34, B_35)) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_38])).
% 9.80/3.76  tff(c_8281, plain, (k10_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7387, c_49])).
% 9.80/3.76  tff(c_8358, plain, (k10_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_8281])).
% 9.80/3.76  tff(c_42, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.80/3.76  tff(c_447, plain, (![B_86, A_87]: (r1_xboole_0(k2_relat_1(B_86), A_87) | k10_relat_1(B_86, A_87)!=k1_xboole_0 | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.80/3.76  tff(c_26, plain, (![A_22, C_24, B_23]: (r1_xboole_0(A_22, C_24) | ~r1_xboole_0(B_23, C_24) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.80/3.76  tff(c_5452, plain, (![A_244, A_245, B_246]: (r1_xboole_0(A_244, A_245) | ~r1_tarski(A_244, k2_relat_1(B_246)) | k10_relat_1(B_246, A_245)!=k1_xboole_0 | ~v1_relat_1(B_246))), inference(resolution, [status(thm)], [c_447, c_26])).
% 9.80/3.76  tff(c_5484, plain, (![A_245]: (r1_xboole_0('#skF_2', A_245) | k10_relat_1('#skF_4', A_245)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_5452])).
% 9.80/3.76  tff(c_5861, plain, (![A_249]: (r1_xboole_0('#skF_2', A_249) | k10_relat_1('#skF_4', A_249)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5484])).
% 9.80/3.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.80/3.76  tff(c_814, plain, (![A_121, B_122, C_123]: (r1_tarski(A_121, k2_xboole_0(B_122, C_123)) | ~r1_tarski(k4_xboole_0(A_121, B_122), C_123))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.80/3.76  tff(c_1105, plain, (![A_132, B_133]: (r1_tarski(A_132, k2_xboole_0(B_133, k4_xboole_0(A_132, B_133))))), inference(resolution, [status(thm)], [c_6, c_814])).
% 9.80/3.76  tff(c_28, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, B_26) | ~r1_xboole_0(A_25, C_27) | ~r1_tarski(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.80/3.76  tff(c_1130, plain, (![A_132, B_133]: (r1_tarski(A_132, B_133) | ~r1_xboole_0(A_132, k4_xboole_0(A_132, B_133)))), inference(resolution, [status(thm)], [c_1105, c_28])).
% 9.80/3.76  tff(c_19437, plain, (![B_397]: (r1_tarski('#skF_2', B_397) | k10_relat_1('#skF_4', k4_xboole_0('#skF_2', B_397))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_5861, c_1130])).
% 9.80/3.76  tff(c_19477, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8358, c_19437])).
% 9.80/3.76  tff(c_19518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_19477])).
% 9.80/3.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.80/3.76  
% 9.80/3.76  Inference rules
% 9.80/3.76  ----------------------
% 9.80/3.76  #Ref     : 0
% 9.80/3.76  #Sup     : 4705
% 9.80/3.76  #Fact    : 0
% 9.80/3.76  #Define  : 0
% 9.80/3.76  #Split   : 7
% 9.80/3.76  #Chain   : 0
% 9.80/3.76  #Close   : 0
% 9.80/3.76  
% 9.80/3.76  Ordering : KBO
% 9.80/3.76  
% 9.80/3.76  Simplification rules
% 9.80/3.76  ----------------------
% 9.80/3.76  #Subsume      : 395
% 9.80/3.76  #Demod        : 4323
% 9.80/3.76  #Tautology    : 3003
% 9.80/3.76  #SimpNegUnit  : 9
% 9.80/3.76  #BackRed      : 3
% 9.80/3.76  
% 9.80/3.76  #Partial instantiations: 0
% 9.80/3.76  #Strategies tried      : 1
% 9.80/3.76  
% 9.80/3.76  Timing (in seconds)
% 9.80/3.76  ----------------------
% 9.80/3.77  Preprocessing        : 0.44
% 9.80/3.77  Parsing              : 0.25
% 9.80/3.77  CNF conversion       : 0.03
% 9.80/3.77  Main loop            : 2.55
% 9.80/3.77  Inferencing          : 0.60
% 9.80/3.77  Reduction            : 1.19
% 9.80/3.77  Demodulation         : 1.00
% 9.80/3.77  BG Simplification    : 0.07
% 9.80/3.77  Subsumption          : 0.54
% 9.80/3.77  Abstraction          : 0.11
% 9.80/3.77  MUC search           : 0.00
% 9.80/3.77  Cooper               : 0.00
% 9.80/3.77  Total                : 3.02
% 9.80/3.77  Index Insertion      : 0.00
% 9.80/3.77  Index Deletion       : 0.00
% 9.80/3.77  Index Matching       : 0.00
% 9.80/3.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
