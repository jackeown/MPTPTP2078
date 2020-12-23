%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 148 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 296 expanded)
%              Number of equality atoms :   34 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_34,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_tarski(C_5,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1761,plain,(
    ! [B_132,A_133,C_134] :
      ( ~ r1_tarski(B_132,'#skF_1'(A_133,B_132,C_134))
      | k2_xboole_0(A_133,C_134) = B_132
      | ~ r1_tarski(C_134,B_132)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1765,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(B_4,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_1761])).

tff(c_1779,plain,(
    ! [A_135,B_136] :
      ( k2_xboole_0(A_135,B_136) = B_136
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1765])).

tff(c_1878,plain,(
    ! [A_10] : k2_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_1779])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_403,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(k4_xboole_0(A_74,B_75),C_76)
      | ~ r1_tarski(A_74,k2_xboole_0(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_577,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k1_xboole_0
      | ~ r1_tarski(A_93,k2_xboole_0(B_94,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_403,c_75])).

tff(c_629,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_577])).

tff(c_28,plain,(
    ! [A_23,B_24] : k6_subset_1(A_23,B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [C_27,A_25,B_26] :
      ( k6_subset_1(k10_relat_1(C_27,A_25),k10_relat_1(C_27,B_26)) = k10_relat_1(C_27,k6_subset_1(A_25,B_26))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1406,plain,(
    ! [C_120,A_121,B_122] :
      ( k4_xboole_0(k10_relat_1(C_120,A_121),k10_relat_1(C_120,B_122)) = k10_relat_1(C_120,k4_xboole_0(A_121,B_122))
      | ~ v1_funct_1(C_120)
      | ~ v1_relat_1(C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_30])).

tff(c_1422,plain,(
    ! [C_120,B_122] :
      ( k10_relat_1(C_120,k4_xboole_0(B_122,B_122)) = k1_xboole_0
      | ~ v1_funct_1(C_120)
      | ~ v1_relat_1(C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_629])).

tff(c_5416,plain,(
    ! [C_182] :
      ( k10_relat_1(C_182,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_1422])).

tff(c_5419,plain,
    ( k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_5416])).

tff(c_5422,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5419])).

tff(c_703,plain,(
    ! [B_96,A_97] :
      ( k9_relat_1(B_96,k10_relat_1(B_96,A_97)) = A_97
      | ~ r1_tarski(A_97,k2_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_732,plain,(
    ! [B_96] :
      ( k9_relat_1(B_96,k10_relat_1(B_96,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_16,c_703])).

tff(c_5426,plain,
    ( k9_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5422,c_732])).

tff(c_5436,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5426])).

tff(c_38,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_110,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [A_42,A_21,B_22] :
      ( r1_tarski(A_42,k2_xboole_0(A_21,B_22))
      | ~ r1_tarski(A_42,A_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_864,plain,(
    ! [A_102,A_103] :
      ( k4_xboole_0(A_102,A_103) = k1_xboole_0
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(resolution,[status(thm)],[c_124,c_577])).

tff(c_931,plain,(
    k4_xboole_0(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_864])).

tff(c_1415,plain,
    ( k10_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_931])).

tff(c_1472,plain,(
    k10_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1415])).

tff(c_36,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_126,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,k2_relat_1('#skF_4'))
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_110])).

tff(c_711,plain,(
    ! [A_42] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_42)) = A_42
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_126,c_703])).

tff(c_10155,plain,(
    ! [A_257] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_257)) = A_257
      | ~ r1_tarski(A_257,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_711])).

tff(c_10197,plain,
    ( k9_relat_1('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1472,c_10155])).

tff(c_10227,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5436,c_10197])).

tff(c_282,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(A_61,k2_xboole_0(B_62,C_63))
      | ~ r1_tarski(k4_xboole_0(A_61,B_62),C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_314,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(B_12,A_11)) ),
    inference(resolution,[status(thm)],[c_18,c_282])).

tff(c_3805,plain,(
    ! [A_161,B_162] : k2_xboole_0(A_161,k2_xboole_0(B_162,A_161)) = k2_xboole_0(B_162,A_161) ),
    inference(resolution,[status(thm)],[c_314,c_1779])).

tff(c_313,plain,(
    ! [A_61,B_62,B_22] : r1_tarski(A_61,k2_xboole_0(B_62,k2_xboole_0(k4_xboole_0(A_61,B_62),B_22))) ),
    inference(resolution,[status(thm)],[c_26,c_282])).

tff(c_3876,plain,(
    ! [A_61,A_161] : r1_tarski(A_61,k2_xboole_0(k4_xboole_0(A_61,A_161),A_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3805,c_313])).

tff(c_10282,plain,(
    r1_tarski('#skF_2',k2_xboole_0(k1_xboole_0,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10227,c_3876])).

tff(c_10349,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_10282])).

tff(c_10351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_10349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.53  
% 6.10/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.53  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.10/2.53  
% 6.10/2.53  %Foreground sorts:
% 6.10/2.53  
% 6.10/2.53  
% 6.10/2.53  %Background operators:
% 6.10/2.53  
% 6.10/2.53  
% 6.10/2.53  %Foreground operators:
% 6.10/2.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.10/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.10/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.10/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.10/2.53  tff('#skF_2', type, '#skF_2': $i).
% 6.10/2.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.10/2.53  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.10/2.53  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.10/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.10/2.53  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.10/2.53  
% 6.45/2.55  tff(f_95, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 6.45/2.55  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.45/2.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.45/2.55  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 6.45/2.55  tff(f_54, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.45/2.55  tff(f_68, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.45/2.55  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.45/2.55  tff(f_70, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.45/2.55  tff(f_76, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 6.45/2.55  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 6.45/2.55  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.45/2.55  tff(f_62, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.45/2.55  tff(c_34, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.45/2.55  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.45/2.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.45/2.55  tff(c_10, plain, (![C_5, A_3, B_4]: (r1_tarski(C_5, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.45/2.55  tff(c_1761, plain, (![B_132, A_133, C_134]: (~r1_tarski(B_132, '#skF_1'(A_133, B_132, C_134)) | k2_xboole_0(A_133, C_134)=B_132 | ~r1_tarski(C_134, B_132) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.45/2.55  tff(c_1765, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(B_4, B_4) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_1761])).
% 6.45/2.55  tff(c_1779, plain, (![A_135, B_136]: (k2_xboole_0(A_135, B_136)=B_136 | ~r1_tarski(A_135, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1765])).
% 6.45/2.55  tff(c_1878, plain, (![A_10]: (k2_xboole_0(k1_xboole_0, A_10)=A_10)), inference(resolution, [status(thm)], [c_16, c_1779])).
% 6.45/2.55  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.45/2.55  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.45/2.55  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.45/2.55  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.45/2.55  tff(c_403, plain, (![A_74, B_75, C_76]: (r1_tarski(k4_xboole_0(A_74, B_75), C_76) | ~r1_tarski(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.45/2.55  tff(c_58, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.45/2.55  tff(c_75, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_58])).
% 6.45/2.55  tff(c_577, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k1_xboole_0 | ~r1_tarski(A_93, k2_xboole_0(B_94, k1_xboole_0)))), inference(resolution, [status(thm)], [c_403, c_75])).
% 6.45/2.55  tff(c_629, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_577])).
% 6.45/2.55  tff(c_28, plain, (![A_23, B_24]: (k6_subset_1(A_23, B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.45/2.55  tff(c_30, plain, (![C_27, A_25, B_26]: (k6_subset_1(k10_relat_1(C_27, A_25), k10_relat_1(C_27, B_26))=k10_relat_1(C_27, k6_subset_1(A_25, B_26)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.45/2.55  tff(c_1406, plain, (![C_120, A_121, B_122]: (k4_xboole_0(k10_relat_1(C_120, A_121), k10_relat_1(C_120, B_122))=k10_relat_1(C_120, k4_xboole_0(A_121, B_122)) | ~v1_funct_1(C_120) | ~v1_relat_1(C_120))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_30])).
% 6.45/2.55  tff(c_1422, plain, (![C_120, B_122]: (k10_relat_1(C_120, k4_xboole_0(B_122, B_122))=k1_xboole_0 | ~v1_funct_1(C_120) | ~v1_relat_1(C_120))), inference(superposition, [status(thm), theory('equality')], [c_1406, c_629])).
% 6.45/2.55  tff(c_5416, plain, (![C_182]: (k10_relat_1(C_182, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_182) | ~v1_relat_1(C_182))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_1422])).
% 6.45/2.55  tff(c_5419, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_5416])).
% 6.45/2.55  tff(c_5422, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5419])).
% 6.45/2.55  tff(c_703, plain, (![B_96, A_97]: (k9_relat_1(B_96, k10_relat_1(B_96, A_97))=A_97 | ~r1_tarski(A_97, k2_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.45/2.55  tff(c_732, plain, (![B_96]: (k9_relat_1(B_96, k10_relat_1(B_96, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_16, c_703])).
% 6.45/2.55  tff(c_5426, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5422, c_732])).
% 6.45/2.55  tff(c_5436, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5426])).
% 6.45/2.55  tff(c_38, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.45/2.55  tff(c_110, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.45/2.55  tff(c_124, plain, (![A_42, A_21, B_22]: (r1_tarski(A_42, k2_xboole_0(A_21, B_22)) | ~r1_tarski(A_42, A_21))), inference(resolution, [status(thm)], [c_26, c_110])).
% 6.45/2.55  tff(c_864, plain, (![A_102, A_103]: (k4_xboole_0(A_102, A_103)=k1_xboole_0 | ~r1_tarski(A_102, A_103))), inference(resolution, [status(thm)], [c_124, c_577])).
% 6.45/2.55  tff(c_931, plain, (k4_xboole_0(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_864])).
% 6.45/2.55  tff(c_1415, plain, (k10_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1406, c_931])).
% 6.45/2.55  tff(c_1472, plain, (k10_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1415])).
% 6.45/2.55  tff(c_36, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.45/2.55  tff(c_126, plain, (![A_42]: (r1_tarski(A_42, k2_relat_1('#skF_4')) | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_110])).
% 6.45/2.55  tff(c_711, plain, (![A_42]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_42))=A_42 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_126, c_703])).
% 6.45/2.55  tff(c_10155, plain, (![A_257]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_257))=A_257 | ~r1_tarski(A_257, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_711])).
% 6.45/2.55  tff(c_10197, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3') | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1472, c_10155])).
% 6.45/2.55  tff(c_10227, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5436, c_10197])).
% 6.45/2.55  tff(c_282, plain, (![A_61, B_62, C_63]: (r1_tarski(A_61, k2_xboole_0(B_62, C_63)) | ~r1_tarski(k4_xboole_0(A_61, B_62), C_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.45/2.55  tff(c_314, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(B_12, A_11)))), inference(resolution, [status(thm)], [c_18, c_282])).
% 6.45/2.55  tff(c_3805, plain, (![A_161, B_162]: (k2_xboole_0(A_161, k2_xboole_0(B_162, A_161))=k2_xboole_0(B_162, A_161))), inference(resolution, [status(thm)], [c_314, c_1779])).
% 6.45/2.55  tff(c_313, plain, (![A_61, B_62, B_22]: (r1_tarski(A_61, k2_xboole_0(B_62, k2_xboole_0(k4_xboole_0(A_61, B_62), B_22))))), inference(resolution, [status(thm)], [c_26, c_282])).
% 6.45/2.55  tff(c_3876, plain, (![A_61, A_161]: (r1_tarski(A_61, k2_xboole_0(k4_xboole_0(A_61, A_161), A_161)))), inference(superposition, [status(thm), theory('equality')], [c_3805, c_313])).
% 6.45/2.55  tff(c_10282, plain, (r1_tarski('#skF_2', k2_xboole_0(k1_xboole_0, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10227, c_3876])).
% 6.45/2.55  tff(c_10349, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_10282])).
% 6.45/2.55  tff(c_10351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_10349])).
% 6.45/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.55  
% 6.45/2.55  Inference rules
% 6.45/2.55  ----------------------
% 6.45/2.55  #Ref     : 0
% 6.45/2.55  #Sup     : 2501
% 6.45/2.55  #Fact    : 0
% 6.45/2.55  #Define  : 0
% 6.45/2.55  #Split   : 2
% 6.45/2.55  #Chain   : 0
% 6.45/2.55  #Close   : 0
% 6.45/2.55  
% 6.45/2.55  Ordering : KBO
% 6.45/2.55  
% 6.45/2.55  Simplification rules
% 6.45/2.55  ----------------------
% 6.45/2.55  #Subsume      : 219
% 6.45/2.55  #Demod        : 1997
% 6.45/2.55  #Tautology    : 1653
% 6.45/2.55  #SimpNegUnit  : 1
% 6.45/2.55  #BackRed      : 4
% 6.45/2.55  
% 6.45/2.55  #Partial instantiations: 0
% 6.45/2.55  #Strategies tried      : 1
% 6.45/2.55  
% 6.45/2.55  Timing (in seconds)
% 6.45/2.55  ----------------------
% 6.45/2.55  Preprocessing        : 0.48
% 6.45/2.55  Parsing              : 0.25
% 6.45/2.55  CNF conversion       : 0.03
% 6.45/2.55  Main loop            : 1.21
% 6.45/2.55  Inferencing          : 0.35
% 6.45/2.55  Reduction            : 0.50
% 6.45/2.55  Demodulation         : 0.39
% 6.45/2.55  BG Simplification    : 0.04
% 6.45/2.55  Subsumption          : 0.26
% 6.45/2.55  Abstraction          : 0.06
% 6.45/2.55  MUC search           : 0.00
% 6.45/2.55  Cooper               : 0.00
% 6.45/2.55  Total                : 1.73
% 6.45/2.55  Index Insertion      : 0.00
% 6.45/2.55  Index Deletion       : 0.00
% 6.45/2.55  Index Matching       : 0.00
% 6.45/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
