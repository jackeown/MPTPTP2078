%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 109 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 210 expanded)
%              Number of equality atoms :   34 (  54 expanded)
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

tff(f_92,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_136,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_149,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_32])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_439,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k4_xboole_0(A_67,B_68),C_69)
      | ~ r1_tarski(A_67,k2_xboole_0(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_940,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k1_xboole_0
      | ~ r1_tarski(A_93,k2_xboole_0(B_94,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_439,c_20])).

tff(c_993,plain,(
    ! [B_94] : k4_xboole_0(k2_xboole_0(B_94,k1_xboole_0),B_94) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_940])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_250,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(B_51,C_50)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_393,plain,(
    ! [A_64,A_65,B_66] :
      ( r1_tarski(A_64,A_65)
      | ~ r1_tarski(A_64,k4_xboole_0(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_18,c_250])).

tff(c_1385,plain,(
    ! [A_110,A_111,B_112] :
      ( r1_tarski(A_110,A_111)
      | k4_xboole_0(A_110,k4_xboole_0(A_111,B_112)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_1579,plain,(
    ! [A_117,B_118] : r1_tarski(k2_xboole_0(k4_xboole_0(A_117,B_118),k1_xboole_0),A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_1385])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_328,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_58,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_250])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_341,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,k1_relat_1('#skF_3'))
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_328,c_12])).

tff(c_1651,plain,(
    ! [B_118] : r1_tarski(k4_xboole_0('#skF_1',B_118),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1579,c_341])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_87,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_24,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1182,plain,(
    ! [C_98,A_99,B_100] :
      ( k4_xboole_0(k10_relat_1(C_98,A_99),k10_relat_1(C_98,B_100)) = k10_relat_1(C_98,k4_xboole_0(A_99,B_100))
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_1204,plain,(
    ! [C_98,B_100] :
      ( k10_relat_1(C_98,k4_xboole_0(B_100,B_100)) = k1_xboole_0
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1182,c_108])).

tff(c_1219,plain,(
    ! [C_101] :
      ( k10_relat_1(C_101,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_101)
      | ~ v1_relat_1(C_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1204])).

tff(c_1222,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1219])).

tff(c_1225,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1222])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( k6_subset_1(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21)) = k9_relat_1(C_22,k6_subset_1(A_20,B_21))
      | ~ v2_funct_1(C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1455,plain,(
    ! [C_113,A_114,B_115] :
      ( k4_xboole_0(k9_relat_1(C_113,A_114),k9_relat_1(C_113,B_115)) = k9_relat_1(C_113,k4_xboole_0(A_114,B_115))
      | ~ v2_funct_1(C_113)
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_26])).

tff(c_38,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_103,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_1482,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1455,c_103])).

tff(c_1507,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_1482])).

tff(c_920,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,k10_relat_1(B_92,k9_relat_1(B_92,A_91)))
      | ~ r1_tarski(A_91,k1_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4662,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(A_192,k10_relat_1(B_193,k9_relat_1(B_193,A_192))) = k1_xboole_0
      | ~ r1_tarski(A_192,k1_relat_1(B_193))
      | ~ v1_relat_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_920,c_10])).

tff(c_4811,plain,
    ( k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_4662])).

tff(c_4862,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1651,c_1225,c_4811])).

tff(c_148,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | k4_xboole_0(A_39,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_20])).

tff(c_4948,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4862,c_148])).

tff(c_4989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_4948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/2.00  
% 4.97/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/2.00  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.97/2.00  
% 4.97/2.00  %Foreground sorts:
% 4.97/2.00  
% 4.97/2.00  
% 4.97/2.00  %Background operators:
% 4.97/2.00  
% 4.97/2.00  
% 4.97/2.00  %Foreground operators:
% 4.97/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.97/2.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.97/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.97/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.97/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.97/2.00  tff('#skF_2', type, '#skF_2': $i).
% 4.97/2.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.97/2.00  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.97/2.00  tff('#skF_3', type, '#skF_3': $i).
% 4.97/2.00  tff('#skF_1', type, '#skF_1': $i).
% 4.97/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/2.00  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.97/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.97/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.97/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.97/2.00  
% 5.09/2.02  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.09/2.02  tff(f_92, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.09/2.02  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.09/2.02  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.09/2.02  tff(f_53, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.09/2.02  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.09/2.02  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.09/2.02  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.09/2.02  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.09/2.02  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 5.09/2.02  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 5.09/2.02  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.09/2.02  tff(c_136, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.09/2.02  tff(c_32, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.09/2.02  tff(c_149, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_32])).
% 5.09/2.02  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.09/2.02  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.09/2.02  tff(c_439, plain, (![A_67, B_68, C_69]: (r1_tarski(k4_xboole_0(A_67, B_68), C_69) | ~r1_tarski(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.09/2.02  tff(c_20, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.09/2.02  tff(c_940, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k1_xboole_0 | ~r1_tarski(A_93, k2_xboole_0(B_94, k1_xboole_0)))), inference(resolution, [status(thm)], [c_439, c_20])).
% 5.09/2.02  tff(c_993, plain, (![B_94]: (k4_xboole_0(k2_xboole_0(B_94, k1_xboole_0), B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_940])).
% 5.09/2.02  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.09/2.02  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/2.02  tff(c_250, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(B_51, C_50) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.09/2.02  tff(c_393, plain, (![A_64, A_65, B_66]: (r1_tarski(A_64, A_65) | ~r1_tarski(A_64, k4_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_18, c_250])).
% 5.09/2.02  tff(c_1385, plain, (![A_110, A_111, B_112]: (r1_tarski(A_110, A_111) | k4_xboole_0(A_110, k4_xboole_0(A_111, B_112))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_393])).
% 5.09/2.02  tff(c_1579, plain, (![A_117, B_118]: (r1_tarski(k2_xboole_0(k4_xboole_0(A_117, B_118), k1_xboole_0), A_117))), inference(superposition, [status(thm), theory('equality')], [c_993, c_1385])).
% 5.09/2.02  tff(c_36, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.09/2.02  tff(c_328, plain, (![A_58]: (r1_tarski(A_58, k1_relat_1('#skF_3')) | ~r1_tarski(A_58, '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_250])).
% 5.09/2.02  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/2.02  tff(c_341, plain, (![A_5, B_6]: (r1_tarski(A_5, k1_relat_1('#skF_3')) | ~r1_tarski(k2_xboole_0(A_5, B_6), '#skF_1'))), inference(resolution, [status(thm)], [c_328, c_12])).
% 5.09/2.02  tff(c_1651, plain, (![B_118]: (r1_tarski(k4_xboole_0('#skF_1', B_118), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_1579, c_341])).
% 5.09/2.02  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.09/2.02  tff(c_87, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.09/2.02  tff(c_108, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 5.09/2.02  tff(c_24, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.09/2.02  tff(c_28, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.09/2.02  tff(c_1182, plain, (![C_98, A_99, B_100]: (k4_xboole_0(k10_relat_1(C_98, A_99), k10_relat_1(C_98, B_100))=k10_relat_1(C_98, k4_xboole_0(A_99, B_100)) | ~v1_funct_1(C_98) | ~v1_relat_1(C_98))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 5.09/2.02  tff(c_1204, plain, (![C_98, B_100]: (k10_relat_1(C_98, k4_xboole_0(B_100, B_100))=k1_xboole_0 | ~v1_funct_1(C_98) | ~v1_relat_1(C_98))), inference(superposition, [status(thm), theory('equality')], [c_1182, c_108])).
% 5.09/2.02  tff(c_1219, plain, (![C_101]: (k10_relat_1(C_101, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_101) | ~v1_relat_1(C_101))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1204])).
% 5.09/2.02  tff(c_1222, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1219])).
% 5.09/2.02  tff(c_1225, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1222])).
% 5.09/2.02  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.09/2.02  tff(c_26, plain, (![C_22, A_20, B_21]: (k6_subset_1(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21))=k9_relat_1(C_22, k6_subset_1(A_20, B_21)) | ~v2_funct_1(C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.09/2.02  tff(c_1455, plain, (![C_113, A_114, B_115]: (k4_xboole_0(k9_relat_1(C_113, A_114), k9_relat_1(C_113, B_115))=k9_relat_1(C_113, k4_xboole_0(A_114, B_115)) | ~v2_funct_1(C_113) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_26])).
% 5.09/2.02  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.09/2.02  tff(c_103, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_87])).
% 5.09/2.02  tff(c_1482, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1455, c_103])).
% 5.09/2.02  tff(c_1507, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_1482])).
% 5.09/2.02  tff(c_920, plain, (![A_91, B_92]: (r1_tarski(A_91, k10_relat_1(B_92, k9_relat_1(B_92, A_91))) | ~r1_tarski(A_91, k1_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/2.02  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.09/2.02  tff(c_4662, plain, (![A_192, B_193]: (k4_xboole_0(A_192, k10_relat_1(B_193, k9_relat_1(B_193, A_192)))=k1_xboole_0 | ~r1_tarski(A_192, k1_relat_1(B_193)) | ~v1_relat_1(B_193))), inference(resolution, [status(thm)], [c_920, c_10])).
% 5.09/2.02  tff(c_4811, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1507, c_4662])).
% 5.09/2.02  tff(c_4862, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1651, c_1225, c_4811])).
% 5.09/2.02  tff(c_148, plain, (![A_39]: (k1_xboole_0=A_39 | k4_xboole_0(A_39, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_20])).
% 5.09/2.02  tff(c_4948, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4862, c_148])).
% 5.09/2.02  tff(c_4989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_4948])).
% 5.09/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.02  
% 5.09/2.02  Inference rules
% 5.09/2.02  ----------------------
% 5.09/2.02  #Ref     : 0
% 5.09/2.02  #Sup     : 1194
% 5.09/2.02  #Fact    : 0
% 5.09/2.02  #Define  : 0
% 5.09/2.02  #Split   : 3
% 5.09/2.02  #Chain   : 0
% 5.09/2.02  #Close   : 0
% 5.09/2.02  
% 5.09/2.02  Ordering : KBO
% 5.09/2.02  
% 5.09/2.02  Simplification rules
% 5.09/2.02  ----------------------
% 5.09/2.02  #Subsume      : 143
% 5.09/2.02  #Demod        : 983
% 5.09/2.02  #Tautology    : 658
% 5.09/2.02  #SimpNegUnit  : 2
% 5.09/2.02  #BackRed      : 0
% 5.09/2.02  
% 5.09/2.02  #Partial instantiations: 0
% 5.09/2.02  #Strategies tried      : 1
% 5.09/2.02  
% 5.09/2.02  Timing (in seconds)
% 5.09/2.02  ----------------------
% 5.09/2.02  Preprocessing        : 0.36
% 5.09/2.02  Parsing              : 0.20
% 5.09/2.02  CNF conversion       : 0.02
% 5.09/2.02  Main loop            : 0.88
% 5.09/2.02  Inferencing          : 0.27
% 5.09/2.02  Reduction            : 0.33
% 5.09/2.02  Demodulation         : 0.25
% 5.09/2.02  BG Simplification    : 0.03
% 5.09/2.02  Subsumption          : 0.18
% 5.09/2.02  Abstraction          : 0.04
% 5.09/2.02  MUC search           : 0.00
% 5.09/2.02  Cooper               : 0.00
% 5.09/2.02  Total                : 1.27
% 5.09/2.02  Index Insertion      : 0.00
% 5.09/2.02  Index Deletion       : 0.00
% 5.09/2.02  Index Matching       : 0.00
% 5.09/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
