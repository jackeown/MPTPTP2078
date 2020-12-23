%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 121 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 274 expanded)
%              Number of equality atoms :   36 (  63 expanded)
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [C_12,A_10,B_11] :
      ( k6_subset_1(k10_relat_1(C_12,A_10),k10_relat_1(C_12,B_11)) = k10_relat_1(C_12,k6_subset_1(A_10,B_11))
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_545,plain,(
    ! [C_61,A_62,B_63] :
      ( k4_xboole_0(k10_relat_1(C_61,A_62),k10_relat_1(C_61,B_63)) = k10_relat_1(C_61,k4_xboole_0(A_62,B_63))
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_558,plain,(
    ! [C_61,B_63] :
      ( k10_relat_1(C_61,k4_xboole_0(B_63,B_63)) = k1_xboole_0
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_66])).

tff(c_570,plain,(
    ! [C_64] :
      ( k10_relat_1(C_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_558])).

tff(c_573,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_570])).

tff(c_576,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_573])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_95,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,k9_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_38,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_414,plain,(
    ! [A_52] :
      ( k4_xboole_0(A_52,k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0
      | ~ r1_tarski(A_52,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_209,c_10])).

tff(c_434,plain,(
    ! [A_3] :
      ( k4_xboole_0(A_3,k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0
      | k4_xboole_0(A_3,k9_relat_1('#skF_3','#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_414])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,k10_relat_1(B_14,k9_relat_1(B_14,A_13)))
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k10_relat_1(B_39,k9_relat_1(B_39,A_40)),A_40)
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1555,plain,(
    ! [B_101,A_102] :
      ( k10_relat_1(B_101,k9_relat_1(B_101,A_102)) = A_102
      | ~ r1_tarski(A_102,k10_relat_1(B_101,k9_relat_1(B_101,A_102)))
      | ~ v2_funct_1(B_101)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_1768,plain,(
    ! [B_104,A_105] :
      ( k10_relat_1(B_104,k9_relat_1(B_104,A_105)) = A_105
      | ~ v2_funct_1(B_104)
      | ~ v1_funct_1(B_104)
      | ~ r1_tarski(A_105,k1_relat_1(B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_1555])).

tff(c_1783,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1768])).

tff(c_1798,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1783])).

tff(c_33,plain,(
    ! [C_12,A_10,B_11] :
      ( k4_xboole_0(k10_relat_1(C_12,A_10),k10_relat_1(C_12,B_11)) = k10_relat_1(C_12,k4_xboole_0(A_10,B_11))
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_1827,plain,(
    ! [B_11] :
      ( k10_relat_1('#skF_3',k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),B_11)) = k4_xboole_0('#skF_1',k10_relat_1('#skF_3',B_11))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1798,c_33])).

tff(c_2160,plain,(
    ! [B_111] : k10_relat_1('#skF_3',k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),B_111)) = k4_xboole_0('#skF_1',k10_relat_1('#skF_3',B_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1827])).

tff(c_2204,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k10_relat_1('#skF_3',k1_xboole_0)
    | k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_2160])).

tff(c_2237,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_576,c_2204])).

tff(c_180,plain,(
    ! [A_34,B_35,A_36] :
      ( r1_tarski(A_34,B_35)
      | ~ r1_tarski(A_34,A_36)
      | k4_xboole_0(A_36,B_35) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_95])).

tff(c_193,plain,(
    ! [A_3,B_35,B_4] :
      ( r1_tarski(A_3,B_35)
      | k4_xboole_0(B_4,B_35) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_2304,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')))
      | k4_xboole_0(A_113,'#skF_1') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_193])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [A_5,A_40,B_39] :
      ( r1_tarski(A_5,A_40)
      | ~ r1_tarski(A_5,k10_relat_1(B_39,k9_relat_1(B_39,A_40)))
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_227,c_12])).

tff(c_2320,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,'#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k4_xboole_0(A_113,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2304,c_242])).

tff(c_2372,plain,(
    ! [A_114] :
      ( r1_tarski(A_114,'#skF_2')
      | k4_xboole_0(A_114,'#skF_1') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_2320])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2410,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2372,c_22])).

tff(c_2427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.74  
% 4.15/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.74  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.15/1.74  
% 4.15/1.74  %Foreground sorts:
% 4.15/1.74  
% 4.15/1.74  
% 4.15/1.74  %Background operators:
% 4.15/1.74  
% 4.15/1.74  
% 4.15/1.74  %Foreground operators:
% 4.15/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.15/1.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.15/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.15/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.15/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.15/1.74  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.15/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.15/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.15/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.15/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.15/1.74  
% 4.15/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.15/1.75  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.15/1.75  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.15/1.75  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.15/1.75  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 4.15/1.75  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.15/1.75  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.15/1.75  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.15/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/1.75  tff(c_50, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.15/1.75  tff(c_66, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_50])).
% 4.15/1.75  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.75  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.75  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.75  tff(c_14, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.15/1.75  tff(c_16, plain, (![C_12, A_10, B_11]: (k6_subset_1(k10_relat_1(C_12, A_10), k10_relat_1(C_12, B_11))=k10_relat_1(C_12, k6_subset_1(A_10, B_11)) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.15/1.75  tff(c_545, plain, (![C_61, A_62, B_63]: (k4_xboole_0(k10_relat_1(C_61, A_62), k10_relat_1(C_61, B_63))=k10_relat_1(C_61, k4_xboole_0(A_62, B_63)) | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 4.15/1.75  tff(c_558, plain, (![C_61, B_63]: (k10_relat_1(C_61, k4_xboole_0(B_63, B_63))=k1_xboole_0 | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(superposition, [status(thm), theory('equality')], [c_545, c_66])).
% 4.15/1.75  tff(c_570, plain, (![C_64]: (k10_relat_1(C_64, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_558])).
% 4.15/1.75  tff(c_573, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_570])).
% 4.15/1.75  tff(c_576, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_573])).
% 4.15/1.75  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.15/1.75  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.75  tff(c_95, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.15/1.75  tff(c_209, plain, (![A_38]: (r1_tarski(A_38, k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_38, k9_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_95])).
% 4.15/1.75  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.15/1.75  tff(c_414, plain, (![A_52]: (k4_xboole_0(A_52, k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0 | ~r1_tarski(A_52, k9_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_209, c_10])).
% 4.15/1.75  tff(c_434, plain, (![A_3]: (k4_xboole_0(A_3, k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0 | k4_xboole_0(A_3, k9_relat_1('#skF_3', '#skF_1'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_414])).
% 4.15/1.75  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.75  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k10_relat_1(B_14, k9_relat_1(B_14, A_13))) | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.15/1.75  tff(c_227, plain, (![B_39, A_40]: (r1_tarski(k10_relat_1(B_39, k9_relat_1(B_39, A_40)), A_40) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.15/1.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/1.75  tff(c_1555, plain, (![B_101, A_102]: (k10_relat_1(B_101, k9_relat_1(B_101, A_102))=A_102 | ~r1_tarski(A_102, k10_relat_1(B_101, k9_relat_1(B_101, A_102))) | ~v2_funct_1(B_101) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_227, c_2])).
% 4.15/1.75  tff(c_1768, plain, (![B_104, A_105]: (k10_relat_1(B_104, k9_relat_1(B_104, A_105))=A_105 | ~v2_funct_1(B_104) | ~v1_funct_1(B_104) | ~r1_tarski(A_105, k1_relat_1(B_104)) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_18, c_1555])).
% 4.15/1.75  tff(c_1783, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1768])).
% 4.15/1.75  tff(c_1798, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1783])).
% 4.15/1.75  tff(c_33, plain, (![C_12, A_10, B_11]: (k4_xboole_0(k10_relat_1(C_12, A_10), k10_relat_1(C_12, B_11))=k10_relat_1(C_12, k4_xboole_0(A_10, B_11)) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 4.15/1.75  tff(c_1827, plain, (![B_11]: (k10_relat_1('#skF_3', k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), B_11))=k4_xboole_0('#skF_1', k10_relat_1('#skF_3', B_11)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1798, c_33])).
% 4.15/1.75  tff(c_2160, plain, (![B_111]: (k10_relat_1('#skF_3', k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), B_111))=k4_xboole_0('#skF_1', k10_relat_1('#skF_3', B_111)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1827])).
% 4.15/1.75  tff(c_2204, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k10_relat_1('#skF_3', k1_xboole_0) | k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_434, c_2160])).
% 4.15/1.75  tff(c_2237, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_576, c_2204])).
% 4.15/1.75  tff(c_180, plain, (![A_34, B_35, A_36]: (r1_tarski(A_34, B_35) | ~r1_tarski(A_34, A_36) | k4_xboole_0(A_36, B_35)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_95])).
% 4.15/1.75  tff(c_193, plain, (![A_3, B_35, B_4]: (r1_tarski(A_3, B_35) | k4_xboole_0(B_4, B_35)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_180])).
% 4.15/1.75  tff(c_2304, plain, (![A_113]: (r1_tarski(A_113, k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))) | k4_xboole_0(A_113, '#skF_1')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2237, c_193])).
% 4.15/1.75  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.15/1.75  tff(c_242, plain, (![A_5, A_40, B_39]: (r1_tarski(A_5, A_40) | ~r1_tarski(A_5, k10_relat_1(B_39, k9_relat_1(B_39, A_40))) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_227, c_12])).
% 4.15/1.75  tff(c_2320, plain, (![A_113]: (r1_tarski(A_113, '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(A_113, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2304, c_242])).
% 4.15/1.75  tff(c_2372, plain, (![A_114]: (r1_tarski(A_114, '#skF_2') | k4_xboole_0(A_114, '#skF_1')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_2320])).
% 4.15/1.75  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.75  tff(c_2410, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2372, c_22])).
% 4.15/1.75  tff(c_2427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_2410])).
% 4.15/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.75  
% 4.15/1.75  Inference rules
% 4.15/1.75  ----------------------
% 4.15/1.75  #Ref     : 0
% 4.15/1.75  #Sup     : 588
% 4.15/1.75  #Fact    : 0
% 4.15/1.75  #Define  : 0
% 4.15/1.75  #Split   : 8
% 4.15/1.75  #Chain   : 0
% 4.15/1.75  #Close   : 0
% 4.15/1.75  
% 4.15/1.75  Ordering : KBO
% 4.15/1.75  
% 4.15/1.75  Simplification rules
% 4.15/1.75  ----------------------
% 4.15/1.75  #Subsume      : 135
% 4.15/1.75  #Demod        : 364
% 4.15/1.75  #Tautology    : 158
% 4.15/1.75  #SimpNegUnit  : 2
% 4.15/1.75  #BackRed      : 0
% 4.15/1.75  
% 4.15/1.75  #Partial instantiations: 0
% 4.15/1.75  #Strategies tried      : 1
% 4.15/1.75  
% 4.15/1.75  Timing (in seconds)
% 4.15/1.75  ----------------------
% 4.15/1.76  Preprocessing        : 0.29
% 4.15/1.76  Parsing              : 0.16
% 4.15/1.76  CNF conversion       : 0.02
% 4.15/1.76  Main loop            : 0.71
% 4.15/1.76  Inferencing          : 0.21
% 4.15/1.76  Reduction            : 0.24
% 4.15/1.76  Demodulation         : 0.17
% 4.15/1.76  BG Simplification    : 0.02
% 4.15/1.76  Subsumption          : 0.18
% 4.15/1.76  Abstraction          : 0.04
% 4.15/1.76  MUC search           : 0.00
% 4.15/1.76  Cooper               : 0.00
% 4.15/1.76  Total                : 1.02
% 4.15/1.76  Index Insertion      : 0.00
% 4.15/1.76  Index Deletion       : 0.00
% 4.15/1.76  Index Matching       : 0.00
% 4.15/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
