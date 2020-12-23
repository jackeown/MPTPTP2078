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
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   69 (  97 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 177 expanded)
%              Number of equality atoms :   28 (  44 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_59,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_63,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_32])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_396,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(k2_xboole_0(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_426,plain,(
    ! [A_59,B_60,B_61] : r1_tarski(A_59,k2_xboole_0(k2_xboole_0(A_59,B_60),B_61)) ),
    inference(resolution,[status(thm)],[c_22,c_396])).

tff(c_547,plain,(
    ! [A_67,B_68,B_69] : r1_tarski(k4_xboole_0(A_67,B_68),k2_xboole_0(A_67,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_426])).

tff(c_567,plain,(
    ! [B_68] : r1_tarski(k4_xboole_0('#skF_1',B_68),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_547])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_24,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1264,plain,(
    ! [C_96,A_97,B_98] :
      ( k4_xboole_0(k10_relat_1(C_96,A_97),k10_relat_1(C_96,B_98)) = k10_relat_1(C_96,k4_xboole_0(A_97,B_98))
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_1295,plain,(
    ! [C_96,B_98] :
      ( k10_relat_1(C_96,k4_xboole_0(B_98,B_98)) = k1_xboole_0
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_134])).

tff(c_1310,plain,(
    ! [C_99] :
      ( k10_relat_1(C_99,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1295])).

tff(c_1313,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1310])).

tff(c_1316,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1313])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( k6_subset_1(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21)) = k9_relat_1(C_22,k6_subset_1(A_20,B_21))
      | ~ v2_funct_1(C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1674,plain,(
    ! [C_110,A_111,B_112] :
      ( k4_xboole_0(k9_relat_1(C_110,A_111),k9_relat_1(C_110,B_112)) = k9_relat_1(C_110,k4_xboole_0(A_111,B_112))
      | ~ v2_funct_1(C_110)
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_26])).

tff(c_38,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_129,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_1707,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1674,c_129])).

tff(c_1735,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_1707])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k10_relat_1(B_27,k9_relat_1(B_27,A_26)))
      | ~ r1_tarski(A_26,k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1750,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1735,c_30])).

tff(c_1758,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_567,c_1316,c_1750])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_307,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_327,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_307])).

tff(c_1764,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1758,c_327])).

tff(c_1777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_1764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:04:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.55  
% 3.20/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.55  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.55  
% 3.20/1.55  %Foreground sorts:
% 3.20/1.55  
% 3.20/1.55  
% 3.20/1.55  %Background operators:
% 3.20/1.55  
% 3.20/1.55  
% 3.20/1.55  %Foreground operators:
% 3.20/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.20/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.55  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.20/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.20/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.55  
% 3.20/1.56  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.20/1.56  tff(f_88, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.20/1.56  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.20/1.56  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.20/1.56  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.20/1.56  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.20/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.56  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.20/1.56  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 3.20/1.56  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.20/1.56  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.20/1.56  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.56  tff(c_59, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.56  tff(c_32, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.56  tff(c_63, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_32])).
% 3.20/1.56  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.56  tff(c_36, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.56  tff(c_64, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.56  tff(c_90, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_64])).
% 3.20/1.56  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.56  tff(c_89, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_18, c_64])).
% 3.20/1.56  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.56  tff(c_396, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(k2_xboole_0(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.56  tff(c_426, plain, (![A_59, B_60, B_61]: (r1_tarski(A_59, k2_xboole_0(k2_xboole_0(A_59, B_60), B_61)))), inference(resolution, [status(thm)], [c_22, c_396])).
% 3.20/1.56  tff(c_547, plain, (![A_67, B_68, B_69]: (r1_tarski(k4_xboole_0(A_67, B_68), k2_xboole_0(A_67, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_426])).
% 3.20/1.56  tff(c_567, plain, (![B_68]: (r1_tarski(k4_xboole_0('#skF_1', B_68), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_547])).
% 3.20/1.56  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.56  tff(c_106, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.56  tff(c_134, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_106])).
% 3.20/1.56  tff(c_24, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.56  tff(c_28, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.56  tff(c_1264, plain, (![C_96, A_97, B_98]: (k4_xboole_0(k10_relat_1(C_96, A_97), k10_relat_1(C_96, B_98))=k10_relat_1(C_96, k4_xboole_0(A_97, B_98)) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 3.20/1.56  tff(c_1295, plain, (![C_96, B_98]: (k10_relat_1(C_96, k4_xboole_0(B_98, B_98))=k1_xboole_0 | ~v1_funct_1(C_96) | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_134])).
% 3.20/1.56  tff(c_1310, plain, (![C_99]: (k10_relat_1(C_99, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1295])).
% 3.20/1.56  tff(c_1313, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1310])).
% 3.20/1.56  tff(c_1316, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1313])).
% 3.20/1.56  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.56  tff(c_26, plain, (![C_22, A_20, B_21]: (k6_subset_1(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21))=k9_relat_1(C_22, k6_subset_1(A_20, B_21)) | ~v2_funct_1(C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.56  tff(c_1674, plain, (![C_110, A_111, B_112]: (k4_xboole_0(k9_relat_1(C_110, A_111), k9_relat_1(C_110, B_112))=k9_relat_1(C_110, k4_xboole_0(A_111, B_112)) | ~v2_funct_1(C_110) | ~v1_funct_1(C_110) | ~v1_relat_1(C_110))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_26])).
% 3.20/1.56  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.56  tff(c_129, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_106])).
% 3.20/1.56  tff(c_1707, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1674, c_129])).
% 3.20/1.56  tff(c_1735, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_1707])).
% 3.20/1.56  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(A_26, k10_relat_1(B_27, k9_relat_1(B_27, A_26))) | ~r1_tarski(A_26, k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.20/1.56  tff(c_1750, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0)) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1735, c_30])).
% 3.20/1.56  tff(c_1758, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_567, c_1316, c_1750])).
% 3.20/1.56  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.56  tff(c_307, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.56  tff(c_327, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_307])).
% 3.20/1.56  tff(c_1764, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1758, c_327])).
% 3.20/1.56  tff(c_1777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_1764])).
% 3.20/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.56  
% 3.20/1.56  Inference rules
% 3.20/1.56  ----------------------
% 3.20/1.56  #Ref     : 0
% 3.20/1.56  #Sup     : 427
% 3.20/1.56  #Fact    : 0
% 3.20/1.56  #Define  : 0
% 3.20/1.56  #Split   : 2
% 3.20/1.56  #Chain   : 0
% 3.20/1.56  #Close   : 0
% 3.20/1.56  
% 3.20/1.56  Ordering : KBO
% 3.20/1.56  
% 3.20/1.56  Simplification rules
% 3.20/1.56  ----------------------
% 3.20/1.56  #Subsume      : 2
% 3.20/1.56  #Demod        : 328
% 3.20/1.56  #Tautology    : 296
% 3.20/1.56  #SimpNegUnit  : 1
% 3.20/1.56  #BackRed      : 0
% 3.20/1.56  
% 3.20/1.56  #Partial instantiations: 0
% 3.20/1.56  #Strategies tried      : 1
% 3.20/1.56  
% 3.20/1.56  Timing (in seconds)
% 3.20/1.56  ----------------------
% 3.20/1.57  Preprocessing        : 0.33
% 3.20/1.57  Parsing              : 0.18
% 3.20/1.57  CNF conversion       : 0.02
% 3.20/1.57  Main loop            : 0.44
% 3.20/1.57  Inferencing          : 0.15
% 3.20/1.57  Reduction            : 0.16
% 3.20/1.57  Demodulation         : 0.12
% 3.20/1.57  BG Simplification    : 0.02
% 3.20/1.57  Subsumption          : 0.08
% 3.20/1.57  Abstraction          : 0.03
% 3.20/1.57  MUC search           : 0.00
% 3.20/1.57  Cooper               : 0.00
% 3.20/1.57  Total                : 0.81
% 3.20/1.57  Index Insertion      : 0.00
% 3.20/1.57  Index Deletion       : 0.00
% 3.20/1.57  Index Matching       : 0.00
% 3.20/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
