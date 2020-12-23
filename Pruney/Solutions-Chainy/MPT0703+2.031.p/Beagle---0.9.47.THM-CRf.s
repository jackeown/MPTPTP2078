%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 171 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 326 expanded)
%              Number of equality atoms :   33 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_781,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(k2_xboole_0(A_107,C_108),B_109)
      | ~ r1_tarski(C_108,B_109)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k2_xboole_0(B_66,C_67))
      | ~ r1_tarski(k4_xboole_0(A_65,B_66),C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_286,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(B_69,A_68)) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_301,plain,(
    ! [B_69,A_68] :
      ( k2_xboole_0(B_69,A_68) = A_68
      | ~ r1_tarski(k2_xboole_0(B_69,A_68),A_68) ) ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_789,plain,(
    ! [A_107,B_109] :
      ( k2_xboole_0(A_107,B_109) = B_109
      | ~ r1_tarski(B_109,B_109)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(resolution,[status(thm)],[c_781,c_301])).

tff(c_1806,plain,(
    ! [A_129,B_130] :
      ( k2_xboole_0(A_129,B_130) = B_130
      | ~ r1_tarski(A_129,B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_789])).

tff(c_1905,plain,(
    ! [A_9] : k2_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_12,c_1806])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(k2_xboole_0(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_34,B_36] : r1_tarski(A_34,k2_xboole_0(A_34,B_36)) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_445,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(k4_xboole_0(A_90,B_91),C_92)
      | ~ r1_tarski(A_90,k2_xboole_0(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_544,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(A_101,B_102) = k1_xboole_0
      | ~ r1_tarski(A_101,k2_xboole_0(B_102,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_445,c_89])).

tff(c_598,plain,(
    ! [A_34] : k4_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_544])).

tff(c_22,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2047,plain,(
    ! [C_132,A_133,B_134] :
      ( k4_xboole_0(k10_relat_1(C_132,A_133),k10_relat_1(C_132,B_134)) = k10_relat_1(C_132,k4_xboole_0(A_133,B_134))
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_24])).

tff(c_2103,plain,(
    ! [C_132,A_133] :
      ( k10_relat_1(C_132,k4_xboole_0(A_133,A_133)) = k1_xboole_0
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_2047])).

tff(c_3936,plain,(
    ! [C_164] :
      ( k10_relat_1(C_164,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_164)
      | ~ v1_relat_1(C_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_2103])).

tff(c_3939,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_3936])).

tff(c_3942,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3939])).

tff(c_1316,plain,(
    ! [B_121,A_122] :
      ( k9_relat_1(B_121,k10_relat_1(B_121,A_122)) = A_122
      | ~ r1_tarski(A_122,k2_relat_1(B_121))
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1349,plain,(
    ! [B_121] :
      ( k9_relat_1(B_121,k10_relat_1(B_121,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_12,c_1316])).

tff(c_3946,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3942,c_1349])).

tff(c_3956,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3946])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_123,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_46,A_34,B_36] :
      ( r1_tarski(A_46,k2_xboole_0(A_34,B_36))
      | ~ r1_tarski(A_46,A_34) ) ),
    inference(resolution,[status(thm)],[c_56,c_123])).

tff(c_864,plain,(
    ! [A_112,A_113] :
      ( k4_xboole_0(A_112,A_113) = k1_xboole_0
      | ~ r1_tarski(A_112,A_113) ) ),
    inference(resolution,[status(thm)],[c_139,c_544])).

tff(c_949,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_864])).

tff(c_2099,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_2047])).

tff(c_2110,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2099])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_142,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_46,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_123])).

tff(c_1327,plain,(
    ! [A_46] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_46)) = A_46
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_46,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_142,c_1316])).

tff(c_10568,plain,(
    ! [A_257] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_257)) = A_257
      | ~ r1_tarski(A_257,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1327])).

tff(c_10610,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_10568])).

tff(c_10640,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3956,c_10610])).

tff(c_284,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(B_11,A_10)) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_5141,plain,(
    ! [A_181,B_182] : k2_xboole_0(A_181,k2_xboole_0(B_182,A_181)) = k2_xboole_0(B_182,A_181) ),
    inference(resolution,[status(thm)],[c_284,c_1806])).

tff(c_283,plain,(
    ! [A_65,B_66,B_36] : r1_tarski(A_65,k2_xboole_0(B_66,k2_xboole_0(k4_xboole_0(A_65,B_66),B_36))) ),
    inference(resolution,[status(thm)],[c_56,c_247])).

tff(c_5212,plain,(
    ! [A_65,A_181] : r1_tarski(A_65,k2_xboole_0(k4_xboole_0(A_65,A_181),A_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5141,c_283])).

tff(c_10681,plain,(
    r1_tarski('#skF_1',k2_xboole_0(k1_xboole_0,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10640,c_5212])).

tff(c_10756,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_10681])).

tff(c_10758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_10756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.34  
% 6.45/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.34  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.45/2.34  
% 6.45/2.34  %Foreground sorts:
% 6.45/2.34  
% 6.45/2.34  
% 6.45/2.34  %Background operators:
% 6.45/2.34  
% 6.45/2.34  
% 6.45/2.34  %Foreground operators:
% 6.45/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.45/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.45/2.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.45/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.45/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.45/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.45/2.35  
% 6.45/2.36  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 6.45/2.36  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.45/2.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.45/2.36  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.45/2.36  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.45/2.36  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.45/2.36  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.45/2.36  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.45/2.36  tff(f_61, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.45/2.36  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 6.45/2.36  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 6.45/2.36  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.45/2.36  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.45/2.36  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.45/2.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.45/2.36  tff(c_781, plain, (![A_107, C_108, B_109]: (r1_tarski(k2_xboole_0(A_107, C_108), B_109) | ~r1_tarski(C_108, B_109) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.45/2.36  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.45/2.36  tff(c_247, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k2_xboole_0(B_66, C_67)) | ~r1_tarski(k4_xboole_0(A_65, B_66), C_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.45/2.36  tff(c_286, plain, (![A_68, B_69]: (r1_tarski(A_68, k2_xboole_0(B_69, A_68)))), inference(resolution, [status(thm)], [c_14, c_247])).
% 6.45/2.36  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.45/2.36  tff(c_301, plain, (![B_69, A_68]: (k2_xboole_0(B_69, A_68)=A_68 | ~r1_tarski(k2_xboole_0(B_69, A_68), A_68))), inference(resolution, [status(thm)], [c_286, c_2])).
% 6.45/2.36  tff(c_789, plain, (![A_107, B_109]: (k2_xboole_0(A_107, B_109)=B_109 | ~r1_tarski(B_109, B_109) | ~r1_tarski(A_107, B_109))), inference(resolution, [status(thm)], [c_781, c_301])).
% 6.45/2.36  tff(c_1806, plain, (![A_129, B_130]: (k2_xboole_0(A_129, B_130)=B_130 | ~r1_tarski(A_129, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_789])).
% 6.45/2.36  tff(c_1905, plain, (![A_9]: (k2_xboole_0(k1_xboole_0, A_9)=A_9)), inference(resolution, [status(thm)], [c_12, c_1806])).
% 6.45/2.36  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.45/2.36  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.45/2.36  tff(c_51, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(k2_xboole_0(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.45/2.36  tff(c_56, plain, (![A_34, B_36]: (r1_tarski(A_34, k2_xboole_0(A_34, B_36)))), inference(resolution, [status(thm)], [c_6, c_51])).
% 6.45/2.36  tff(c_445, plain, (![A_90, B_91, C_92]: (r1_tarski(k4_xboole_0(A_90, B_91), C_92) | ~r1_tarski(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.45/2.36  tff(c_69, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.45/2.36  tff(c_89, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_69])).
% 6.45/2.36  tff(c_544, plain, (![A_101, B_102]: (k4_xboole_0(A_101, B_102)=k1_xboole_0 | ~r1_tarski(A_101, k2_xboole_0(B_102, k1_xboole_0)))), inference(resolution, [status(thm)], [c_445, c_89])).
% 6.45/2.36  tff(c_598, plain, (![A_34]: (k4_xboole_0(A_34, A_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_544])).
% 6.45/2.36  tff(c_22, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.45/2.36  tff(c_24, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.45/2.36  tff(c_2047, plain, (![C_132, A_133, B_134]: (k4_xboole_0(k10_relat_1(C_132, A_133), k10_relat_1(C_132, B_134))=k10_relat_1(C_132, k4_xboole_0(A_133, B_134)) | ~v1_funct_1(C_132) | ~v1_relat_1(C_132))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_24])).
% 6.45/2.36  tff(c_2103, plain, (![C_132, A_133]: (k10_relat_1(C_132, k4_xboole_0(A_133, A_133))=k1_xboole_0 | ~v1_funct_1(C_132) | ~v1_relat_1(C_132))), inference(superposition, [status(thm), theory('equality')], [c_598, c_2047])).
% 6.45/2.36  tff(c_3936, plain, (![C_164]: (k10_relat_1(C_164, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_164) | ~v1_relat_1(C_164))), inference(demodulation, [status(thm), theory('equality')], [c_598, c_2103])).
% 6.45/2.36  tff(c_3939, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_3936])).
% 6.45/2.36  tff(c_3942, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3939])).
% 6.45/2.36  tff(c_1316, plain, (![B_121, A_122]: (k9_relat_1(B_121, k10_relat_1(B_121, A_122))=A_122 | ~r1_tarski(A_122, k2_relat_1(B_121)) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.45/2.36  tff(c_1349, plain, (![B_121]: (k9_relat_1(B_121, k10_relat_1(B_121, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_12, c_1316])).
% 6.45/2.36  tff(c_3946, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3942, c_1349])).
% 6.45/2.36  tff(c_3956, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3946])).
% 6.45/2.36  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.45/2.36  tff(c_123, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.45/2.36  tff(c_139, plain, (![A_46, A_34, B_36]: (r1_tarski(A_46, k2_xboole_0(A_34, B_36)) | ~r1_tarski(A_46, A_34))), inference(resolution, [status(thm)], [c_56, c_123])).
% 6.45/2.36  tff(c_864, plain, (![A_112, A_113]: (k4_xboole_0(A_112, A_113)=k1_xboole_0 | ~r1_tarski(A_112, A_113))), inference(resolution, [status(thm)], [c_139, c_544])).
% 6.45/2.36  tff(c_949, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_864])).
% 6.45/2.36  tff(c_2099, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_949, c_2047])).
% 6.45/2.36  tff(c_2110, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2099])).
% 6.45/2.36  tff(c_30, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.45/2.36  tff(c_142, plain, (![A_46]: (r1_tarski(A_46, k2_relat_1('#skF_3')) | ~r1_tarski(A_46, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_123])).
% 6.45/2.36  tff(c_1327, plain, (![A_46]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_46))=A_46 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_46, '#skF_1'))), inference(resolution, [status(thm)], [c_142, c_1316])).
% 6.45/2.36  tff(c_10568, plain, (![A_257]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_257))=A_257 | ~r1_tarski(A_257, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1327])).
% 6.45/2.36  tff(c_10610, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_10568])).
% 6.45/2.36  tff(c_10640, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3956, c_10610])).
% 6.45/2.36  tff(c_284, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(B_11, A_10)))), inference(resolution, [status(thm)], [c_14, c_247])).
% 6.45/2.36  tff(c_5141, plain, (![A_181, B_182]: (k2_xboole_0(A_181, k2_xboole_0(B_182, A_181))=k2_xboole_0(B_182, A_181))), inference(resolution, [status(thm)], [c_284, c_1806])).
% 6.45/2.36  tff(c_283, plain, (![A_65, B_66, B_36]: (r1_tarski(A_65, k2_xboole_0(B_66, k2_xboole_0(k4_xboole_0(A_65, B_66), B_36))))), inference(resolution, [status(thm)], [c_56, c_247])).
% 6.45/2.36  tff(c_5212, plain, (![A_65, A_181]: (r1_tarski(A_65, k2_xboole_0(k4_xboole_0(A_65, A_181), A_181)))), inference(superposition, [status(thm), theory('equality')], [c_5141, c_283])).
% 6.45/2.36  tff(c_10681, plain, (r1_tarski('#skF_1', k2_xboole_0(k1_xboole_0, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10640, c_5212])).
% 6.45/2.36  tff(c_10756, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1905, c_10681])).
% 6.45/2.36  tff(c_10758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_10756])).
% 6.45/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.36  
% 6.45/2.36  Inference rules
% 6.45/2.36  ----------------------
% 6.45/2.36  #Ref     : 0
% 6.45/2.36  #Sup     : 2624
% 6.45/2.36  #Fact    : 0
% 6.45/2.36  #Define  : 0
% 6.45/2.36  #Split   : 2
% 6.45/2.36  #Chain   : 0
% 6.45/2.36  #Close   : 0
% 6.45/2.36  
% 6.45/2.36  Ordering : KBO
% 6.45/2.36  
% 6.45/2.36  Simplification rules
% 6.45/2.36  ----------------------
% 6.45/2.36  #Subsume      : 255
% 6.45/2.36  #Demod        : 2083
% 6.45/2.36  #Tautology    : 1683
% 6.45/2.36  #SimpNegUnit  : 1
% 6.45/2.36  #BackRed      : 5
% 6.45/2.36  
% 6.45/2.36  #Partial instantiations: 0
% 6.45/2.36  #Strategies tried      : 1
% 6.45/2.36  
% 6.45/2.36  Timing (in seconds)
% 6.45/2.36  ----------------------
% 6.45/2.36  Preprocessing        : 0.32
% 6.45/2.36  Parsing              : 0.17
% 6.45/2.36  CNF conversion       : 0.02
% 6.45/2.36  Main loop            : 1.27
% 6.45/2.36  Inferencing          : 0.37
% 6.45/2.36  Reduction            : 0.52
% 6.45/2.36  Demodulation         : 0.42
% 6.45/2.36  BG Simplification    : 0.05
% 6.45/2.36  Subsumption          : 0.25
% 6.45/2.36  Abstraction          : 0.07
% 6.45/2.36  MUC search           : 0.00
% 6.45/2.36  Cooper               : 0.00
% 6.45/2.36  Total                : 1.63
% 6.45/2.36  Index Insertion      : 0.00
% 6.45/2.36  Index Deletion       : 0.00
% 6.45/2.36  Index Matching       : 0.00
% 6.45/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
