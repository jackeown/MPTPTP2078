%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:50 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 258 expanded)
%              Number of leaves         :   22 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 638 expanded)
%              Number of equality atoms :   44 ( 244 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    ! [A_18] :
      ( k4_relat_1(A_18) = k2_funct_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_78,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_75])).

tff(c_10,plain,(
    ! [A_9] :
      ( k2_relat_1(k4_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_89,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_82])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_relat_1(k4_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_91,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_106,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_103])).

tff(c_123,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_126,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_126])).

tff(c_132,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_108,plain,(
    ! [A_19,B_20] :
      ( k10_relat_1(A_19,k1_relat_1(B_20)) = k1_relat_1(k5_relat_1(A_19,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_19] :
      ( k1_relat_1(k5_relat_1(A_19,k2_funct_1('#skF_1'))) = k10_relat_1(A_19,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_108])).

tff(c_286,plain,(
    ! [A_26] :
      ( k1_relat_1(k5_relat_1(A_26,k2_funct_1('#skF_1'))) = k10_relat_1(A_26,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_117])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_298,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_71])).

tff(c_307,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_298])).

tff(c_311,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_311])).

tff(c_316,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_325,plain,(
    ! [A_27] :
      ( k4_relat_1(A_27) = k2_funct_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_328,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_325])).

tff(c_331,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_328])).

tff(c_335,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_10])).

tff(c_342,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_335])).

tff(c_338,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_12])).

tff(c_344,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_338])).

tff(c_371,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_2])).

tff(c_374,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_371])).

tff(c_376,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_380,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_376])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_380])).

tff(c_386,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_385,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( k9_relat_1(B_4,k2_relat_1(A_2)) = k2_relat_1(k5_relat_1(A_2,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_390,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_4])).

tff(c_397,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_386,c_390])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:45:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.34  
% 2.22/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.22/1.35  
% 2.22/1.35  %Foreground sorts:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Background operators:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Foreground operators:
% 2.22/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.22/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.35  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.22/1.35  
% 2.22/1.36  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.22/1.36  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.22/1.36  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.22/1.36  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.22/1.36  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.22/1.36  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.22/1.36  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.22/1.36  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.22/1.36  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.36  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.22/1.36  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.36  tff(c_18, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.22/1.36  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.36  tff(c_72, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.36  tff(c_75, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.22/1.36  tff(c_78, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_75])).
% 2.22/1.36  tff(c_10, plain, (![A_9]: (k2_relat_1(k4_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.36  tff(c_82, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 2.22/1.36  tff(c_89, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_82])).
% 2.22/1.36  tff(c_12, plain, (![A_9]: (k1_relat_1(k4_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.36  tff(c_85, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 2.22/1.36  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_85])).
% 2.22/1.36  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.36  tff(c_103, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 2.22/1.36  tff(c_106, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_103])).
% 2.22/1.36  tff(c_123, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.22/1.36  tff(c_126, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_123])).
% 2.22/1.36  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_126])).
% 2.22/1.36  tff(c_132, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_106])).
% 2.22/1.36  tff(c_108, plain, (![A_19, B_20]: (k10_relat_1(A_19, k1_relat_1(B_20))=k1_relat_1(k5_relat_1(A_19, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.36  tff(c_117, plain, (![A_19]: (k1_relat_1(k5_relat_1(A_19, k2_funct_1('#skF_1')))=k10_relat_1(A_19, k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_91, c_108])).
% 2.22/1.36  tff(c_286, plain, (![A_26]: (k1_relat_1(k5_relat_1(A_26, k2_funct_1('#skF_1')))=k10_relat_1(A_26, k2_relat_1('#skF_1')) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_117])).
% 2.22/1.36  tff(c_20, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.36  tff(c_71, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.22/1.36  tff(c_298, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_286, c_71])).
% 2.22/1.36  tff(c_307, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_298])).
% 2.22/1.36  tff(c_311, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_307])).
% 2.22/1.36  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_311])).
% 2.22/1.36  tff(c_316, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.22/1.36  tff(c_325, plain, (![A_27]: (k4_relat_1(A_27)=k2_funct_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.36  tff(c_328, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_325])).
% 2.22/1.36  tff(c_331, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_328])).
% 2.22/1.36  tff(c_335, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_331, c_10])).
% 2.22/1.36  tff(c_342, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_335])).
% 2.22/1.36  tff(c_338, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_331, c_12])).
% 2.22/1.36  tff(c_344, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_338])).
% 2.22/1.36  tff(c_371, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_344, c_2])).
% 2.22/1.36  tff(c_374, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_371])).
% 2.22/1.36  tff(c_376, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_374])).
% 2.22/1.36  tff(c_380, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_376])).
% 2.22/1.36  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_380])).
% 2.22/1.36  tff(c_386, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_374])).
% 2.22/1.36  tff(c_385, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_374])).
% 2.22/1.36  tff(c_4, plain, (![B_4, A_2]: (k9_relat_1(B_4, k2_relat_1(A_2))=k2_relat_1(k5_relat_1(A_2, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.36  tff(c_390, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_385, c_4])).
% 2.22/1.36  tff(c_397, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_386, c_390])).
% 2.22/1.36  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_397])).
% 2.22/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  Inference rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Ref     : 0
% 2.22/1.36  #Sup     : 97
% 2.22/1.36  #Fact    : 0
% 2.22/1.36  #Define  : 0
% 2.22/1.36  #Split   : 4
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 0
% 2.22/1.36  #Demod        : 46
% 2.22/1.36  #Tautology    : 49
% 2.22/1.36  #SimpNegUnit  : 1
% 2.22/1.36  #BackRed      : 0
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.36  Preprocessing        : 0.33
% 2.22/1.36  Parsing              : 0.18
% 2.22/1.37  CNF conversion       : 0.02
% 2.22/1.37  Main loop            : 0.23
% 2.22/1.37  Inferencing          : 0.09
% 2.22/1.37  Reduction            : 0.07
% 2.22/1.37  Demodulation         : 0.05
% 2.22/1.37  BG Simplification    : 0.02
% 2.22/1.37  Subsumption          : 0.04
% 2.22/1.37  Abstraction          : 0.02
% 2.22/1.37  MUC search           : 0.00
% 2.22/1.37  Cooper               : 0.00
% 2.22/1.37  Total                : 0.59
% 2.22/1.37  Index Insertion      : 0.00
% 2.22/1.37  Index Deletion       : 0.00
% 2.22/1.37  Index Matching       : 0.00
% 2.22/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
