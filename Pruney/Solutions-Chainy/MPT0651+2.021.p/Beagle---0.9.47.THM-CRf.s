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
% DateTime   : Thu Dec  3 10:03:50 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 171 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 388 expanded)
%              Number of equality atoms :   48 ( 136 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_74,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_26,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_13] :
      ( k9_relat_1(k6_relat_1(A_13),A_13) = k2_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_89,plain,(
    ! [A_13] : k9_relat_1(k6_relat_1(A_13),A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_85])).

tff(c_159,plain,(
    ! [B_31,A_32] :
      ( k9_relat_1(B_31,k2_relat_1(A_32)) = k2_relat_1(k5_relat_1(A_32,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_188,plain,(
    ! [A_13,B_31] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_13),B_31)) = k9_relat_1(B_31,A_13)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_159])).

tff(c_339,plain,(
    ! [A_38,B_39] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_38),B_39)) = k9_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_188])).

tff(c_106,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_26,B_27)),k2_relat_1(B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [A_26,A_13] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_26,k6_relat_1(A_13))),A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_114,plain,(
    ! [A_26,A_13] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_26,k6_relat_1(A_13))),A_13)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_112])).

tff(c_359,plain,(
    ! [A_13,A_38] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_13),A_38),A_13)
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_114])).

tff(c_393,plain,(
    ! [A_42,A_43] : r1_tarski(k9_relat_1(k6_relat_1(A_42),A_43),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_359])).

tff(c_400,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_393])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    ! [A_25] :
      ( k4_relat_1(A_25) = k2_funct_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_105,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_102])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_132,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_10])).

tff(c_128,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_118])).

tff(c_223,plain,(
    ! [A_33,B_34] :
      ( k1_relat_1(k5_relat_1(A_33,B_34)) = k1_relat_1(A_33)
      | ~ r1_tarski(k2_relat_1(A_33),k1_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,(
    ! [A_33] :
      ( k1_relat_1(k5_relat_1(A_33,k2_funct_1('#skF_1'))) = k1_relat_1(A_33)
      | ~ r1_tarski(k2_relat_1(A_33),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_223])).

tff(c_413,plain,(
    ! [A_45] :
      ( k1_relat_1(k5_relat_1(A_45,k2_funct_1('#skF_1'))) = k1_relat_1(A_45)
      | ~ r1_tarski(k2_relat_1(A_45),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_239])).

tff(c_417,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_400,c_413])).

tff(c_446,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_417])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_446])).

tff(c_449,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_493,plain,(
    ! [A_49] :
      ( k4_relat_1(A_49) = k2_funct_1(A_49)
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_496,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_493])).

tff(c_499,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_496])).

tff(c_509,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_2])).

tff(c_517,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_509])).

tff(c_553,plain,(
    ! [B_54,A_55] :
      ( k9_relat_1(B_54,k2_relat_1(A_55)) = k2_relat_1(k5_relat_1(A_55,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_506,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_8])).

tff(c_515,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_506])).

tff(c_503,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_10])).

tff(c_513,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_503])).

tff(c_4,plain,(
    ! [A_2] :
      ( k9_relat_1(A_2,k1_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_522,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_4])).

tff(c_526,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_522])).

tff(c_533,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_526])).

tff(c_559,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_533])).

tff(c_585,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_517,c_559])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.33  
% 2.12/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.33  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.12/1.33  
% 2.12/1.33  %Foreground sorts:
% 2.12/1.33  
% 2.12/1.33  
% 2.12/1.33  %Background operators:
% 2.12/1.33  
% 2.12/1.33  
% 2.12/1.33  %Foreground operators:
% 2.12/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.12/1.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.12/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.12/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.12/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.33  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.12/1.33  
% 2.55/1.35  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.55/1.35  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.55/1.35  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.55/1.35  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.55/1.35  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.55/1.35  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.55/1.35  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.55/1.35  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.55/1.35  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.55/1.35  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.55/1.35  tff(c_26, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.35  tff(c_63, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.55/1.35  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.35  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.35  tff(c_18, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.55/1.35  tff(c_16, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.55/1.35  tff(c_73, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.35  tff(c_85, plain, (![A_13]: (k9_relat_1(k6_relat_1(A_13), A_13)=k2_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_73])).
% 2.55/1.35  tff(c_89, plain, (![A_13]: (k9_relat_1(k6_relat_1(A_13), A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_85])).
% 2.55/1.35  tff(c_159, plain, (![B_31, A_32]: (k9_relat_1(B_31, k2_relat_1(A_32))=k2_relat_1(k5_relat_1(A_32, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.35  tff(c_188, plain, (![A_13, B_31]: (k2_relat_1(k5_relat_1(k6_relat_1(A_13), B_31))=k9_relat_1(B_31, A_13) | ~v1_relat_1(B_31) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_159])).
% 2.55/1.35  tff(c_339, plain, (![A_38, B_39]: (k2_relat_1(k5_relat_1(k6_relat_1(A_38), B_39))=k9_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_188])).
% 2.55/1.35  tff(c_106, plain, (![A_26, B_27]: (r1_tarski(k2_relat_1(k5_relat_1(A_26, B_27)), k2_relat_1(B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.35  tff(c_112, plain, (![A_26, A_13]: (r1_tarski(k2_relat_1(k5_relat_1(A_26, k6_relat_1(A_13))), A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_18, c_106])).
% 2.55/1.35  tff(c_114, plain, (![A_26, A_13]: (r1_tarski(k2_relat_1(k5_relat_1(A_26, k6_relat_1(A_13))), A_13) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_112])).
% 2.55/1.35  tff(c_359, plain, (![A_13, A_38]: (r1_tarski(k9_relat_1(k6_relat_1(A_13), A_38), A_13) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_114])).
% 2.55/1.35  tff(c_393, plain, (![A_42, A_43]: (r1_tarski(k9_relat_1(k6_relat_1(A_42), A_43), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_359])).
% 2.55/1.35  tff(c_400, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_89, c_393])).
% 2.55/1.35  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.35  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.35  tff(c_99, plain, (![A_25]: (k4_relat_1(A_25)=k2_funct_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.35  tff(c_102, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.55/1.35  tff(c_105, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_102])).
% 2.55/1.35  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.35  tff(c_124, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 2.55/1.35  tff(c_132, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_124])).
% 2.55/1.35  tff(c_10, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.35  tff(c_118, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_10])).
% 2.55/1.35  tff(c_128, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_118])).
% 2.55/1.35  tff(c_223, plain, (![A_33, B_34]: (k1_relat_1(k5_relat_1(A_33, B_34))=k1_relat_1(A_33) | ~r1_tarski(k2_relat_1(A_33), k1_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.35  tff(c_239, plain, (![A_33]: (k1_relat_1(k5_relat_1(A_33, k2_funct_1('#skF_1')))=k1_relat_1(A_33) | ~r1_tarski(k2_relat_1(A_33), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_128, c_223])).
% 2.55/1.35  tff(c_413, plain, (![A_45]: (k1_relat_1(k5_relat_1(A_45, k2_funct_1('#skF_1')))=k1_relat_1(A_45) | ~r1_tarski(k2_relat_1(A_45), k2_relat_1('#skF_1')) | ~v1_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_239])).
% 2.55/1.35  tff(c_417, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_400, c_413])).
% 2.55/1.35  tff(c_446, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_417])).
% 2.55/1.35  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_446])).
% 2.55/1.35  tff(c_449, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.55/1.35  tff(c_493, plain, (![A_49]: (k4_relat_1(A_49)=k2_funct_1(A_49) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.35  tff(c_496, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_493])).
% 2.55/1.35  tff(c_499, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_496])).
% 2.55/1.35  tff(c_509, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_499, c_2])).
% 2.55/1.35  tff(c_517, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_509])).
% 2.55/1.35  tff(c_553, plain, (![B_54, A_55]: (k9_relat_1(B_54, k2_relat_1(A_55))=k2_relat_1(k5_relat_1(A_55, B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.35  tff(c_8, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.35  tff(c_506, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_499, c_8])).
% 2.55/1.35  tff(c_515, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_506])).
% 2.55/1.35  tff(c_503, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_499, c_10])).
% 2.55/1.35  tff(c_513, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_503])).
% 2.55/1.35  tff(c_4, plain, (![A_2]: (k9_relat_1(A_2, k1_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.35  tff(c_522, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_513, c_4])).
% 2.55/1.35  tff(c_526, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_522])).
% 2.55/1.35  tff(c_533, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_526])).
% 2.55/1.35  tff(c_559, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_553, c_533])).
% 2.55/1.35  tff(c_585, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_517, c_559])).
% 2.55/1.35  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_585])).
% 2.55/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  
% 2.55/1.35  Inference rules
% 2.55/1.35  ----------------------
% 2.55/1.35  #Ref     : 0
% 2.55/1.35  #Sup     : 131
% 2.55/1.35  #Fact    : 0
% 2.55/1.35  #Define  : 0
% 2.55/1.35  #Split   : 2
% 2.55/1.35  #Chain   : 0
% 2.55/1.35  #Close   : 0
% 2.55/1.35  
% 2.55/1.35  Ordering : KBO
% 2.55/1.35  
% 2.55/1.35  Simplification rules
% 2.55/1.35  ----------------------
% 2.55/1.35  #Subsume      : 1
% 2.55/1.35  #Demod        : 73
% 2.55/1.35  #Tautology    : 57
% 2.55/1.35  #SimpNegUnit  : 2
% 2.55/1.35  #BackRed      : 0
% 2.55/1.35  
% 2.55/1.35  #Partial instantiations: 0
% 2.55/1.35  #Strategies tried      : 1
% 2.55/1.35  
% 2.55/1.35  Timing (in seconds)
% 2.55/1.35  ----------------------
% 2.55/1.35  Preprocessing        : 0.29
% 2.55/1.35  Parsing              : 0.16
% 2.55/1.35  CNF conversion       : 0.02
% 2.55/1.35  Main loop            : 0.27
% 2.55/1.35  Inferencing          : 0.11
% 2.55/1.35  Reduction            : 0.09
% 2.55/1.35  Demodulation         : 0.06
% 2.55/1.35  BG Simplification    : 0.01
% 2.55/1.35  Subsumption          : 0.04
% 2.55/1.35  Abstraction          : 0.02
% 2.55/1.35  MUC search           : 0.00
% 2.55/1.35  Cooper               : 0.00
% 2.55/1.35  Total                : 0.59
% 2.55/1.35  Index Insertion      : 0.00
% 2.55/1.35  Index Deletion       : 0.00
% 2.55/1.35  Index Matching       : 0.00
% 2.55/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
