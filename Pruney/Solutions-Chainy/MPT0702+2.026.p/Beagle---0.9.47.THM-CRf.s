%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 278 expanded)
%              Number of leaves         :   26 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  113 ( 615 expanded)
%              Number of equality atoms :   30 ( 139 expanded)
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
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_94,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_107,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_59])).

tff(c_143,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(k4_xboole_0(A_39,C_40),B_41)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_168,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k1_xboole_0,B_42)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_143])).

tff(c_188,plain,(
    ! [B_44] : r1_tarski(k1_xboole_0,B_44) ),
    inference(resolution,[status(thm)],[c_6,c_168])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [B_44] : k4_xboole_0(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_10])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [C_18,A_16,B_17] :
      ( k6_subset_1(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17)) = k9_relat_1(C_18,k6_subset_1(A_16,B_17))
      | ~ v2_funct_1(C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_712,plain,(
    ! [C_75,A_76,B_77] :
      ( k4_xboole_0(k9_relat_1(C_75,A_76),k9_relat_1(C_75,B_77)) = k9_relat_1(C_75,k4_xboole_0(A_76,B_77))
      | ~ v2_funct_1(C_75)
      | ~ v1_funct_1(C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_34,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_735,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_72])).

tff(c_754,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_735])).

tff(c_39,plain,(
    ! [C_18,A_16,B_17] :
      ( k4_xboole_0(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17)) = k9_relat_1(C_18,k4_xboole_0(A_16,B_17))
      | ~ v2_funct_1(C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_763,plain,(
    ! [B_17] :
      ( k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_17)) = k4_xboole_0(k1_xboole_0,k9_relat_1('#skF_3',B_17))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_39])).

tff(c_796,plain,(
    ! [B_78] : k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_78)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_199,c_763])).

tff(c_823,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_796])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k10_relat_1(B_22,k9_relat_1(B_22,A_21)),A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_849,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_26])).

tff(c_859,plain,(
    r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_849])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_864,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k10_relat_1('#skF_3',k1_xboole_0)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_859,c_119])).

tff(c_877,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_864])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k10_relat_1(B_20,k9_relat_1(B_20,A_19)))
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_769,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_24])).

tff(c_780,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_769])).

tff(c_1393,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0)
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_780])).

tff(c_1394,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1393])).

tff(c_1400,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1394])).

tff(c_1408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1400])).

tff(c_1409,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1393])).

tff(c_1413,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1409,c_119])).

tff(c_1426,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1413])).

tff(c_1428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.45  
% 2.88/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.45  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.45  
% 2.88/1.45  %Foreground sorts:
% 2.88/1.45  
% 2.88/1.45  
% 2.88/1.45  %Background operators:
% 2.88/1.45  
% 2.88/1.45  
% 2.88/1.45  %Foreground operators:
% 2.88/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.88/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.45  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.88/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.88/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.45  
% 3.22/1.47  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.22/1.47  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.22/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.47  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.22/1.47  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.22/1.47  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.22/1.47  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.22/1.47  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 3.22/1.47  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.22/1.47  tff(c_94, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.47  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.47  tff(c_107, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_28])).
% 3.22/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.47  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.47  tff(c_59, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.47  tff(c_73, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_59])).
% 3.22/1.47  tff(c_143, plain, (![A_39, C_40, B_41]: (r1_tarski(k4_xboole_0(A_39, C_40), B_41) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.47  tff(c_168, plain, (![B_42, A_43]: (r1_tarski(k1_xboole_0, B_42) | ~r1_tarski(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_73, c_143])).
% 3.22/1.47  tff(c_188, plain, (![B_44]: (r1_tarski(k1_xboole_0, B_44))), inference(resolution, [status(thm)], [c_6, c_168])).
% 3.22/1.47  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.47  tff(c_199, plain, (![B_44]: (k4_xboole_0(k1_xboole_0, B_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_10])).
% 3.22/1.47  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.47  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.47  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.47  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.47  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.47  tff(c_20, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.47  tff(c_22, plain, (![C_18, A_16, B_17]: (k6_subset_1(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17))=k9_relat_1(C_18, k6_subset_1(A_16, B_17)) | ~v2_funct_1(C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.47  tff(c_712, plain, (![C_75, A_76, B_77]: (k4_xboole_0(k9_relat_1(C_75, A_76), k9_relat_1(C_75, B_77))=k9_relat_1(C_75, k4_xboole_0(A_76, B_77)) | ~v2_funct_1(C_75) | ~v1_funct_1(C_75) | ~v1_relat_1(C_75))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.22/1.47  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.47  tff(c_72, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_59])).
% 3.22/1.47  tff(c_735, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_712, c_72])).
% 3.22/1.47  tff(c_754, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_735])).
% 3.22/1.47  tff(c_39, plain, (![C_18, A_16, B_17]: (k4_xboole_0(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17))=k9_relat_1(C_18, k4_xboole_0(A_16, B_17)) | ~v2_funct_1(C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.22/1.47  tff(c_763, plain, (![B_17]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_17))=k4_xboole_0(k1_xboole_0, k9_relat_1('#skF_3', B_17)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_754, c_39])).
% 3.22/1.47  tff(c_796, plain, (![B_78]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_78))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_199, c_763])).
% 3.22/1.47  tff(c_823, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_73, c_796])).
% 3.22/1.47  tff(c_26, plain, (![B_22, A_21]: (r1_tarski(k10_relat_1(B_22, k9_relat_1(B_22, A_21)), A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.47  tff(c_849, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_823, c_26])).
% 3.22/1.47  tff(c_859, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_849])).
% 3.22/1.47  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.47  tff(c_108, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.47  tff(c_119, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_108])).
% 3.22/1.47  tff(c_864, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k10_relat_1('#skF_3', k1_xboole_0))!=k1_xboole_0), inference(resolution, [status(thm)], [c_859, c_119])).
% 3.22/1.47  tff(c_877, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_199, c_864])).
% 3.22/1.47  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(A_19, k10_relat_1(B_20, k9_relat_1(B_20, A_19))) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.47  tff(c_769, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0)) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_754, c_24])).
% 3.22/1.47  tff(c_780, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0)) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_769])).
% 3.22/1.47  tff(c_1393, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_877, c_780])).
% 3.22/1.47  tff(c_1394, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1393])).
% 3.22/1.47  tff(c_1400, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1394])).
% 3.22/1.47  tff(c_1408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1400])).
% 3.22/1.47  tff(c_1409, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1393])).
% 3.22/1.47  tff(c_1413, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1409, c_119])).
% 3.22/1.47  tff(c_1426, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_199, c_1413])).
% 3.22/1.47  tff(c_1428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_1426])).
% 3.22/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  Inference rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Ref     : 0
% 3.22/1.47  #Sup     : 319
% 3.22/1.47  #Fact    : 0
% 3.22/1.47  #Define  : 0
% 3.22/1.47  #Split   : 3
% 3.22/1.47  #Chain   : 0
% 3.22/1.47  #Close   : 0
% 3.22/1.47  
% 3.22/1.47  Ordering : KBO
% 3.22/1.47  
% 3.22/1.47  Simplification rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Subsume      : 29
% 3.22/1.47  #Demod        : 236
% 3.22/1.47  #Tautology    : 195
% 3.22/1.47  #SimpNegUnit  : 1
% 3.22/1.47  #BackRed      : 4
% 3.22/1.47  
% 3.22/1.47  #Partial instantiations: 0
% 3.22/1.47  #Strategies tried      : 1
% 3.22/1.47  
% 3.22/1.47  Timing (in seconds)
% 3.22/1.47  ----------------------
% 3.22/1.47  Preprocessing        : 0.30
% 3.22/1.47  Parsing              : 0.17
% 3.22/1.47  CNF conversion       : 0.02
% 3.22/1.47  Main loop            : 0.41
% 3.22/1.47  Inferencing          : 0.14
% 3.22/1.47  Reduction            : 0.14
% 3.22/1.47  Demodulation         : 0.10
% 3.22/1.47  BG Simplification    : 0.02
% 3.22/1.47  Subsumption          : 0.09
% 3.22/1.47  Abstraction          : 0.02
% 3.22/1.47  MUC search           : 0.00
% 3.22/1.47  Cooper               : 0.00
% 3.22/1.47  Total                : 0.74
% 3.22/1.47  Index Insertion      : 0.00
% 3.22/1.47  Index Deletion       : 0.00
% 3.22/1.47  Index Matching       : 0.00
% 3.22/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
