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
% DateTime   : Thu Dec  3 10:03:51 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 162 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 392 expanded)
%              Number of equality atoms :   41 ( 131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_67,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_24] :
      ( k5_relat_1(A_24,k6_relat_1(k2_relat_1(A_24))) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    ! [A_12] :
      ( k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_12)) = k6_relat_1(A_12)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_77])).

tff(c_93,plain,(
    ! [A_12] : k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_89])).

tff(c_198,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_30,B_31)),k1_relat_1(A_30))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_210,plain,(
    ! [A_12] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_12)),k1_relat_1(k6_relat_1(A_12)))
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_198])).

tff(c_225,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_14,c_14,c_210])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_103,plain,(
    ! [A_26] :
      ( k4_relat_1(A_26) = k2_funct_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_109,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_115,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_109])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_145,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_137])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_141,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_131])).

tff(c_231,plain,(
    ! [A_33,B_34] :
      ( k1_relat_1(k5_relat_1(A_33,B_34)) = k1_relat_1(A_33)
      | ~ r1_tarski(k2_relat_1(A_33),k1_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_240,plain,(
    ! [A_33] :
      ( k1_relat_1(k5_relat_1(A_33,k2_funct_1('#skF_1'))) = k1_relat_1(A_33)
      | ~ r1_tarski(k2_relat_1(A_33),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_231])).

tff(c_448,plain,(
    ! [A_44] :
      ( k1_relat_1(k5_relat_1(A_44,k2_funct_1('#skF_1'))) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_240])).

tff(c_452,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_225,c_448])).

tff(c_467,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_452])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_467])).

tff(c_470,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_502,plain,(
    ! [A_47] :
      ( k4_relat_1(A_47) = k2_funct_1(A_47)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_508,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_502])).

tff(c_514,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_508])).

tff(c_524,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_2])).

tff(c_532,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_524])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_521,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_4])).

tff(c_530,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_521])).

tff(c_18,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_relat_1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_582,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_51,B_52)),k1_relat_1(A_51))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1153,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_74),B_75)),k2_relat_1(A_74))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(k4_relat_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_582])).

tff(c_1191,plain,(
    ! [A_74] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_74)),k2_relat_1(A_74))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(A_74))))
      | ~ v1_relat_1(k4_relat_1(A_74))
      | ~ v1_relat_1(A_74)
      | ~ v1_relat_1(k4_relat_1(A_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1153])).

tff(c_1258,plain,(
    ! [A_78] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_78)),k2_relat_1(A_78))
      | ~ v1_relat_1(A_78)
      | ~ v1_relat_1(k4_relat_1(A_78)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1191])).

tff(c_12,plain,(
    ! [B_11,A_9] :
      ( k2_relat_1(k5_relat_1(B_11,A_9)) = k2_relat_1(A_9)
      | ~ r1_tarski(k1_relat_1(A_9),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1330,plain,(
    ! [A_79] :
      ( k2_relat_1(k5_relat_1(A_79,k4_relat_1(A_79))) = k2_relat_1(k4_relat_1(A_79))
      | ~ v1_relat_1(A_79)
      | ~ v1_relat_1(k4_relat_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_1258,c_12])).

tff(c_1365,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_1330])).

tff(c_1375,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_514,c_36,c_530,c_514,c_1365])).

tff(c_1377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_1375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.75  
% 3.46/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.75  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.46/1.75  
% 3.46/1.75  %Foreground sorts:
% 3.46/1.75  
% 3.46/1.75  
% 3.46/1.75  %Background operators:
% 3.46/1.75  
% 3.46/1.75  
% 3.46/1.75  %Foreground operators:
% 3.46/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.46/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.46/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.46/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.46/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.75  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.46/1.75  
% 3.46/1.77  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 3.46/1.77  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.46/1.77  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.46/1.77  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.46/1.77  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 3.46/1.77  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.46/1.77  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.46/1.77  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.46/1.77  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.46/1.77  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.46/1.77  tff(c_30, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.46/1.77  tff(c_67, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.46/1.77  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.46/1.77  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.46/1.77  tff(c_14, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.77  tff(c_16, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.77  tff(c_77, plain, (![A_24]: (k5_relat_1(A_24, k6_relat_1(k2_relat_1(A_24)))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.77  tff(c_89, plain, (![A_12]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_12))=k6_relat_1(A_12) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_77])).
% 3.46/1.77  tff(c_93, plain, (![A_12]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_12))=k6_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_89])).
% 3.46/1.77  tff(c_198, plain, (![A_30, B_31]: (r1_tarski(k1_relat_1(k5_relat_1(A_30, B_31)), k1_relat_1(A_30)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.46/1.77  tff(c_210, plain, (![A_12]: (r1_tarski(k1_relat_1(k6_relat_1(A_12)), k1_relat_1(k6_relat_1(A_12))) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_198])).
% 3.46/1.77  tff(c_225, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_14, c_14, c_210])).
% 3.46/1.77  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.46/1.77  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.46/1.77  tff(c_103, plain, (![A_26]: (k4_relat_1(A_26)=k2_funct_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.77  tff(c_109, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_103])).
% 3.46/1.77  tff(c_115, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_109])).
% 3.46/1.77  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.77  tff(c_137, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 3.46/1.77  tff(c_145, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_137])).
% 3.46/1.77  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.77  tff(c_131, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 3.46/1.77  tff(c_141, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_131])).
% 3.46/1.77  tff(c_231, plain, (![A_33, B_34]: (k1_relat_1(k5_relat_1(A_33, B_34))=k1_relat_1(A_33) | ~r1_tarski(k2_relat_1(A_33), k1_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.46/1.77  tff(c_240, plain, (![A_33]: (k1_relat_1(k5_relat_1(A_33, k2_funct_1('#skF_1')))=k1_relat_1(A_33) | ~r1_tarski(k2_relat_1(A_33), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_141, c_231])).
% 3.46/1.77  tff(c_448, plain, (![A_44]: (k1_relat_1(k5_relat_1(A_44, k2_funct_1('#skF_1')))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k2_relat_1('#skF_1')) | ~v1_relat_1(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_240])).
% 3.46/1.77  tff(c_452, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_225, c_448])).
% 3.46/1.77  tff(c_467, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_452])).
% 3.46/1.77  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_467])).
% 3.46/1.77  tff(c_470, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.46/1.77  tff(c_502, plain, (![A_47]: (k4_relat_1(A_47)=k2_funct_1(A_47) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.77  tff(c_508, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_502])).
% 3.46/1.77  tff(c_514, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_508])).
% 3.46/1.77  tff(c_524, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_514, c_2])).
% 3.46/1.77  tff(c_532, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_524])).
% 3.46/1.77  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.77  tff(c_521, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_514, c_4])).
% 3.46/1.77  tff(c_530, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_521])).
% 3.46/1.77  tff(c_18, plain, (![A_13]: (k5_relat_1(A_13, k6_relat_1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.77  tff(c_582, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(k5_relat_1(A_51, B_52)), k1_relat_1(A_51)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.46/1.77  tff(c_1153, plain, (![A_74, B_75]: (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_74), B_75)), k2_relat_1(A_74)) | ~v1_relat_1(B_75) | ~v1_relat_1(k4_relat_1(A_74)) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_6, c_582])).
% 3.46/1.77  tff(c_1191, plain, (![A_74]: (r1_tarski(k1_relat_1(k4_relat_1(A_74)), k2_relat_1(A_74)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(A_74)))) | ~v1_relat_1(k4_relat_1(A_74)) | ~v1_relat_1(A_74) | ~v1_relat_1(k4_relat_1(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1153])).
% 3.46/1.77  tff(c_1258, plain, (![A_78]: (r1_tarski(k1_relat_1(k4_relat_1(A_78)), k2_relat_1(A_78)) | ~v1_relat_1(A_78) | ~v1_relat_1(k4_relat_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1191])).
% 3.46/1.77  tff(c_12, plain, (![B_11, A_9]: (k2_relat_1(k5_relat_1(B_11, A_9))=k2_relat_1(A_9) | ~r1_tarski(k1_relat_1(A_9), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.46/1.77  tff(c_1330, plain, (![A_79]: (k2_relat_1(k5_relat_1(A_79, k4_relat_1(A_79)))=k2_relat_1(k4_relat_1(A_79)) | ~v1_relat_1(A_79) | ~v1_relat_1(k4_relat_1(A_79)))), inference(resolution, [status(thm)], [c_1258, c_12])).
% 3.46/1.77  tff(c_1365, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_514, c_1330])).
% 3.46/1.77  tff(c_1375, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_514, c_36, c_530, c_514, c_1365])).
% 3.46/1.77  tff(c_1377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_1375])).
% 3.46/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.77  
% 3.46/1.77  Inference rules
% 3.46/1.77  ----------------------
% 3.46/1.77  #Ref     : 0
% 3.46/1.77  #Sup     : 302
% 3.46/1.77  #Fact    : 0
% 3.46/1.77  #Define  : 0
% 3.46/1.77  #Split   : 4
% 3.46/1.77  #Chain   : 0
% 3.46/1.77  #Close   : 0
% 3.46/1.77  
% 3.46/1.77  Ordering : KBO
% 3.46/1.77  
% 3.46/1.77  Simplification rules
% 3.46/1.77  ----------------------
% 3.46/1.77  #Subsume      : 7
% 3.46/1.77  #Demod        : 368
% 3.46/1.77  #Tautology    : 161
% 3.46/1.77  #SimpNegUnit  : 2
% 3.46/1.77  #BackRed      : 0
% 3.46/1.77  
% 3.46/1.77  #Partial instantiations: 0
% 3.46/1.77  #Strategies tried      : 1
% 3.46/1.77  
% 3.46/1.77  Timing (in seconds)
% 3.46/1.77  ----------------------
% 3.46/1.77  Preprocessing        : 0.38
% 3.46/1.77  Parsing              : 0.22
% 3.46/1.77  CNF conversion       : 0.02
% 3.46/1.77  Main loop            : 0.53
% 3.46/1.77  Inferencing          : 0.20
% 3.46/1.77  Reduction            : 0.18
% 3.46/1.77  Demodulation         : 0.14
% 3.46/1.77  BG Simplification    : 0.03
% 3.46/1.77  Subsumption          : 0.08
% 3.46/1.77  Abstraction          : 0.03
% 3.46/1.77  MUC search           : 0.00
% 3.46/1.77  Cooper               : 0.00
% 3.46/1.77  Total                : 0.95
% 3.46/1.77  Index Insertion      : 0.00
% 3.46/1.77  Index Deletion       : 0.00
% 3.46/1.77  Index Matching       : 0.00
% 3.46/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
