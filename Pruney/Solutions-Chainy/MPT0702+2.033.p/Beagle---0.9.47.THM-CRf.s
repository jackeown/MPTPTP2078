%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 182 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_261,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_342,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_48,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_261])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2563,plain,(
    ! [A_128,A_129] :
      ( r1_tarski(A_128,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_128,A_129)
      | ~ r1_tarski(A_129,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_342,c_12])).

tff(c_2609,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k4_xboole_0(A_8,B_9),k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_8,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_2563])).

tff(c_64,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_26])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [C_18,A_16,B_17] :
      ( k6_subset_1(k10_relat_1(C_18,A_16),k10_relat_1(C_18,B_17)) = k10_relat_1(C_18,k6_subset_1(A_16,B_17))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_524,plain,(
    ! [C_57,A_58,B_59] :
      ( k4_xboole_0(k10_relat_1(C_57,A_58),k10_relat_1(C_57,B_59)) = k10_relat_1(C_57,k4_xboole_0(A_58,B_59))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_540,plain,(
    ! [C_57,B_59] :
      ( k10_relat_1(C_57,k4_xboole_0(B_59,B_59)) = k1_xboole_0
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_89])).

tff(c_692,plain,(
    ! [C_66] :
      ( k10_relat_1(C_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_540])).

tff(c_695,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_692])).

tff(c_698,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_695])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( k6_subset_1(k9_relat_1(C_15,A_13),k9_relat_1(C_15,B_14)) = k9_relat_1(C_15,k6_subset_1(A_13,B_14))
      | ~ v2_funct_1(C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_976,plain,(
    ! [C_75,A_76,B_77] :
      ( k4_xboole_0(k9_relat_1(C_75,A_76),k9_relat_1(C_75,B_77)) = k9_relat_1(C_75,k4_xboole_0(A_76,B_77))
      | ~ v2_funct_1(C_75)
      | ~ v1_funct_1(C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_20])).

tff(c_32,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_997,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_86])).

tff(c_1026,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_997])).

tff(c_280,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,k10_relat_1(B_43,k9_relat_1(B_43,A_42)))
      | ~ r1_tarski(A_42,k1_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3100,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(A_139,k10_relat_1(B_140,k9_relat_1(B_140,A_139))) = k1_xboole_0
      | ~ r1_tarski(A_139,k1_relat_1(B_140))
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_280,c_10])).

tff(c_3242,plain,
    ( k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_3100])).

tff(c_3292,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16,c_698,c_3242])).

tff(c_3293,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3292])).

tff(c_3297,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2609,c_3293])).

tff(c_3322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.76  
% 4.08/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.76  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.08/1.76  
% 4.08/1.76  %Foreground sorts:
% 4.08/1.76  
% 4.08/1.76  
% 4.08/1.76  %Background operators:
% 4.08/1.76  
% 4.08/1.76  
% 4.08/1.76  %Foreground operators:
% 4.08/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.08/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.08/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.08/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.08/1.76  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.08/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.08/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.08/1.76  
% 4.44/1.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.44/1.78  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.44/1.78  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.44/1.78  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.44/1.78  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.44/1.78  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.44/1.78  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.44/1.78  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 4.44/1.78  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 4.44/1.78  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.44/1.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.44/1.78  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.44/1.78  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.78  tff(c_261, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.44/1.78  tff(c_342, plain, (![A_48]: (r1_tarski(A_48, k1_relat_1('#skF_3')) | ~r1_tarski(A_48, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_261])).
% 4.44/1.78  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.44/1.78  tff(c_2563, plain, (![A_128, A_129]: (r1_tarski(A_128, k1_relat_1('#skF_3')) | ~r1_tarski(A_128, A_129) | ~r1_tarski(A_129, '#skF_1'))), inference(resolution, [status(thm)], [c_342, c_12])).
% 4.44/1.78  tff(c_2609, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), k1_relat_1('#skF_3')) | ~r1_tarski(A_8, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_2563])).
% 4.44/1.78  tff(c_64, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.78  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.78  tff(c_68, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_26])).
% 4.44/1.78  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.78  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.44/1.78  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.78  tff(c_69, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.78  tff(c_89, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_69])).
% 4.44/1.78  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.44/1.78  tff(c_22, plain, (![C_18, A_16, B_17]: (k6_subset_1(k10_relat_1(C_18, A_16), k10_relat_1(C_18, B_17))=k10_relat_1(C_18, k6_subset_1(A_16, B_17)) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.44/1.78  tff(c_524, plain, (![C_57, A_58, B_59]: (k4_xboole_0(k10_relat_1(C_57, A_58), k10_relat_1(C_57, B_59))=k10_relat_1(C_57, k4_xboole_0(A_58, B_59)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 4.44/1.78  tff(c_540, plain, (![C_57, B_59]: (k10_relat_1(C_57, k4_xboole_0(B_59, B_59))=k1_xboole_0 | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(superposition, [status(thm), theory('equality')], [c_524, c_89])).
% 4.44/1.78  tff(c_692, plain, (![C_66]: (k10_relat_1(C_66, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_540])).
% 4.44/1.78  tff(c_695, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_692])).
% 4.44/1.78  tff(c_698, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_695])).
% 4.44/1.78  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.78  tff(c_20, plain, (![C_15, A_13, B_14]: (k6_subset_1(k9_relat_1(C_15, A_13), k9_relat_1(C_15, B_14))=k9_relat_1(C_15, k6_subset_1(A_13, B_14)) | ~v2_funct_1(C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.78  tff(c_976, plain, (![C_75, A_76, B_77]: (k4_xboole_0(k9_relat_1(C_75, A_76), k9_relat_1(C_75, B_77))=k9_relat_1(C_75, k4_xboole_0(A_76, B_77)) | ~v2_funct_1(C_75) | ~v1_funct_1(C_75) | ~v1_relat_1(C_75))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_20])).
% 4.44/1.78  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.78  tff(c_86, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_69])).
% 4.44/1.78  tff(c_997, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_976, c_86])).
% 4.44/1.78  tff(c_1026, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_997])).
% 4.44/1.78  tff(c_280, plain, (![A_42, B_43]: (r1_tarski(A_42, k10_relat_1(B_43, k9_relat_1(B_43, A_42))) | ~r1_tarski(A_42, k1_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.44/1.78  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.78  tff(c_3100, plain, (![A_139, B_140]: (k4_xboole_0(A_139, k10_relat_1(B_140, k9_relat_1(B_140, A_139)))=k1_xboole_0 | ~r1_tarski(A_139, k1_relat_1(B_140)) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_280, c_10])).
% 4.44/1.78  tff(c_3242, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1026, c_3100])).
% 4.44/1.78  tff(c_3292, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16, c_698, c_3242])).
% 4.44/1.78  tff(c_3293, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_3292])).
% 4.44/1.78  tff(c_3297, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2609, c_3293])).
% 4.44/1.78  tff(c_3322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3297])).
% 4.44/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.78  
% 4.44/1.78  Inference rules
% 4.44/1.78  ----------------------
% 4.44/1.78  #Ref     : 2
% 4.44/1.78  #Sup     : 825
% 4.44/1.78  #Fact    : 0
% 4.44/1.78  #Define  : 0
% 4.44/1.78  #Split   : 4
% 4.44/1.78  #Chain   : 0
% 4.44/1.78  #Close   : 0
% 4.44/1.78  
% 4.44/1.78  Ordering : KBO
% 4.44/1.78  
% 4.44/1.78  Simplification rules
% 4.44/1.78  ----------------------
% 4.44/1.78  #Subsume      : 213
% 4.44/1.78  #Demod        : 438
% 4.44/1.78  #Tautology    : 367
% 4.44/1.78  #SimpNegUnit  : 7
% 4.44/1.78  #BackRed      : 0
% 4.44/1.78  
% 4.44/1.78  #Partial instantiations: 0
% 4.44/1.78  #Strategies tried      : 1
% 4.44/1.78  
% 4.44/1.78  Timing (in seconds)
% 4.44/1.78  ----------------------
% 4.44/1.78  Preprocessing        : 0.30
% 4.44/1.78  Parsing              : 0.16
% 4.44/1.78  CNF conversion       : 0.02
% 4.44/1.78  Main loop            : 0.71
% 4.44/1.78  Inferencing          : 0.21
% 4.44/1.78  Reduction            : 0.26
% 4.44/1.78  Demodulation         : 0.20
% 4.44/1.78  BG Simplification    : 0.03
% 4.44/1.78  Subsumption          : 0.16
% 4.44/1.78  Abstraction          : 0.04
% 4.44/1.78  MUC search           : 0.00
% 4.44/1.78  Cooper               : 0.00
% 4.44/1.78  Total                : 1.03
% 4.44/1.78  Index Insertion      : 0.00
% 4.44/1.78  Index Deletion       : 0.00
% 4.44/1.78  Index Matching       : 0.00
% 4.44/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
