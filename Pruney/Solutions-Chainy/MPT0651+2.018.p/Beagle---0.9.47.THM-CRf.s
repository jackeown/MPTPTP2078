%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:50 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 322 expanded)
%              Number of leaves         :   22 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  122 ( 801 expanded)
%              Number of equality atoms :   40 ( 285 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_78,plain,(
    ! [A_22] :
      ( k4_relat_1(A_22) = k2_funct_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_84,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_81])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_relat_1(k4_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_97,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_91])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k10_relat_1(B_2,A_1),k1_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [A_1] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_1'),A_1),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_151,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_154,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_154])).

tff(c_160,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_215,plain,(
    ! [A_26,B_27] :
      ( k10_relat_1(A_26,k1_relat_1(B_27)) = k1_relat_1(k5_relat_1(A_26,B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_237,plain,(
    ! [A_26] :
      ( k1_relat_1(k5_relat_1(A_26,k2_funct_1('#skF_1'))) = k10_relat_1(A_26,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_215])).

tff(c_279,plain,(
    ! [A_29] :
      ( k1_relat_1(k5_relat_1(A_29,k2_funct_1('#skF_1'))) = k10_relat_1(A_29,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_237])).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_70,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_298,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_70])).

tff(c_309,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_298])).

tff(c_348,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_309])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_348])).

tff(c_353,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_378,plain,(
    ! [A_33] :
      ( k4_relat_1(A_33) = k2_funct_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_381,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_378])).

tff(c_384,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_381])).

tff(c_391,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_10])).

tff(c_397,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_391])).

tff(c_439,plain,(
    ! [A_1] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_1'),A_1),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_2])).

tff(c_445,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_448,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_445])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_448])).

tff(c_454,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_8,plain,(
    ! [A_7] :
      ( k2_relat_1(k4_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_388,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_8])).

tff(c_395,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_388])).

tff(c_402,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_4])).

tff(c_455,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_402])).

tff(c_456,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_456])).

tff(c_459,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_465,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_2])).

tff(c_469,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_397,c_465])).

tff(c_619,plain,(
    ! [B_41,A_42] :
      ( k2_relat_1(k5_relat_1(B_41,A_42)) = k2_relat_1(A_42)
      | ~ r1_tarski(k1_relat_1(A_42),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_634,plain,(
    ! [B_41] :
      ( k2_relat_1(k5_relat_1(B_41,k2_funct_1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_619])).

tff(c_679,plain,(
    ! [B_43] :
      ( k2_relat_1(k5_relat_1(B_43,k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
      | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_395,c_634])).

tff(c_682,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_469,c_679])).

tff(c_694,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_682])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:07:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.40  
% 2.57/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.40  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.57/1.40  
% 2.57/1.40  %Foreground sorts:
% 2.57/1.40  
% 2.57/1.40  
% 2.57/1.40  %Background operators:
% 2.57/1.40  
% 2.57/1.40  
% 2.57/1.40  %Foreground operators:
% 2.57/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.57/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.57/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.40  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.57/1.40  
% 2.57/1.41  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.57/1.41  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.57/1.41  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.57/1.41  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.57/1.41  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.57/1.41  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.57/1.41  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.57/1.41  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.57/1.41  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.57/1.41  tff(c_4, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.41  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.57/1.41  tff(c_18, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.41  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.57/1.41  tff(c_78, plain, (![A_22]: (k4_relat_1(A_22)=k2_funct_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.57/1.41  tff(c_81, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_78])).
% 2.57/1.41  tff(c_84, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_81])).
% 2.57/1.41  tff(c_10, plain, (![A_7]: (k1_relat_1(k4_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.41  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84, c_10])).
% 2.57/1.41  tff(c_97, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_91])).
% 2.57/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k10_relat_1(B_2, A_1), k1_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.41  tff(c_136, plain, (![A_1]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_1'), A_1), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 2.57/1.41  tff(c_151, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_136])).
% 2.57/1.41  tff(c_154, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_151])).
% 2.57/1.41  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_154])).
% 2.57/1.41  tff(c_160, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_136])).
% 2.57/1.41  tff(c_215, plain, (![A_26, B_27]: (k10_relat_1(A_26, k1_relat_1(B_27))=k1_relat_1(k5_relat_1(A_26, B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.41  tff(c_237, plain, (![A_26]: (k1_relat_1(k5_relat_1(A_26, k2_funct_1('#skF_1')))=k10_relat_1(A_26, k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_97, c_215])).
% 2.57/1.41  tff(c_279, plain, (![A_29]: (k1_relat_1(k5_relat_1(A_29, k2_funct_1('#skF_1')))=k10_relat_1(A_29, k2_relat_1('#skF_1')) | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_237])).
% 2.57/1.41  tff(c_24, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.57/1.41  tff(c_70, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.57/1.41  tff(c_298, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_70])).
% 2.57/1.41  tff(c_309, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_298])).
% 2.57/1.41  tff(c_348, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4, c_309])).
% 2.57/1.41  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_348])).
% 2.57/1.41  tff(c_353, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.57/1.41  tff(c_378, plain, (![A_33]: (k4_relat_1(A_33)=k2_funct_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.57/1.41  tff(c_381, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_378])).
% 2.57/1.41  tff(c_384, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_381])).
% 2.57/1.41  tff(c_391, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_384, c_10])).
% 2.57/1.41  tff(c_397, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_391])).
% 2.57/1.41  tff(c_439, plain, (![A_1]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_1'), A_1), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_397, c_2])).
% 2.57/1.41  tff(c_445, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_439])).
% 2.57/1.41  tff(c_448, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_445])).
% 2.57/1.41  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_448])).
% 2.57/1.41  tff(c_454, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_439])).
% 2.57/1.41  tff(c_8, plain, (![A_7]: (k2_relat_1(k4_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.41  tff(c_388, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_384, c_8])).
% 2.57/1.41  tff(c_395, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_388])).
% 2.57/1.41  tff(c_402, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_395, c_4])).
% 2.57/1.41  tff(c_455, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_402])).
% 2.57/1.41  tff(c_456, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_455])).
% 2.57/1.41  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_454, c_456])).
% 2.57/1.41  tff(c_459, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_455])).
% 2.57/1.41  tff(c_465, plain, (r1_tarski(k2_relat_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_459, c_2])).
% 2.57/1.41  tff(c_469, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_397, c_465])).
% 2.57/1.41  tff(c_619, plain, (![B_41, A_42]: (k2_relat_1(k5_relat_1(B_41, A_42))=k2_relat_1(A_42) | ~r1_tarski(k1_relat_1(A_42), k2_relat_1(B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.41  tff(c_634, plain, (![B_41]: (k2_relat_1(k5_relat_1(B_41, k2_funct_1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_1')) | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_397, c_619])).
% 2.57/1.41  tff(c_679, plain, (![B_43]: (k2_relat_1(k5_relat_1(B_43, k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_395, c_634])).
% 2.57/1.41  tff(c_682, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_469, c_679])).
% 2.57/1.41  tff(c_694, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_682])).
% 2.57/1.41  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_694])).
% 2.57/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.41  
% 2.57/1.41  Inference rules
% 2.57/1.41  ----------------------
% 2.57/1.41  #Ref     : 0
% 2.57/1.41  #Sup     : 159
% 2.57/1.41  #Fact    : 0
% 2.57/1.41  #Define  : 0
% 2.57/1.41  #Split   : 6
% 2.57/1.41  #Chain   : 0
% 2.57/1.41  #Close   : 0
% 2.57/1.41  
% 2.57/1.41  Ordering : KBO
% 2.57/1.42  
% 2.57/1.42  Simplification rules
% 2.57/1.42  ----------------------
% 2.57/1.42  #Subsume      : 4
% 2.57/1.42  #Demod        : 121
% 2.57/1.42  #Tautology    : 77
% 2.57/1.42  #SimpNegUnit  : 1
% 2.57/1.42  #BackRed      : 0
% 2.57/1.42  
% 2.57/1.42  #Partial instantiations: 0
% 2.57/1.42  #Strategies tried      : 1
% 2.57/1.42  
% 2.57/1.42  Timing (in seconds)
% 2.57/1.42  ----------------------
% 2.57/1.42  Preprocessing        : 0.32
% 2.57/1.42  Parsing              : 0.17
% 2.57/1.42  CNF conversion       : 0.02
% 2.57/1.42  Main loop            : 0.30
% 2.57/1.42  Inferencing          : 0.11
% 2.57/1.42  Reduction            : 0.09
% 2.57/1.42  Demodulation         : 0.07
% 2.57/1.42  BG Simplification    : 0.02
% 2.57/1.42  Subsumption          : 0.05
% 2.57/1.42  Abstraction          : 0.02
% 2.57/1.42  MUC search           : 0.00
% 2.57/1.42  Cooper               : 0.00
% 2.57/1.42  Total                : 0.65
% 2.57/1.42  Index Insertion      : 0.00
% 2.57/1.42  Index Deletion       : 0.00
% 2.57/1.42  Index Matching       : 0.00
% 2.57/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
