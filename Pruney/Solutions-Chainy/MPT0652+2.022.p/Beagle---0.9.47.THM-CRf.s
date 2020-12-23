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
% DateTime   : Thu Dec  3 10:03:55 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 294 expanded)
%              Number of leaves         :   22 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 733 expanded)
%              Number of equality atoms :   45 ( 281 expanded)
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
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

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

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

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

tff(c_157,plain,(
    ! [A_21] :
      ( k4_relat_1(A_21) = k2_funct_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_157])).

tff(c_163,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_160])).

tff(c_10,plain,(
    ! [A_9] :
      ( k2_relat_1(k4_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_10])).

tff(c_174,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_167])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_relat_1(k4_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_12])).

tff(c_176,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_170])).

tff(c_203,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_2])).

tff(c_206,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_203])).

tff(c_208,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_211,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_211])).

tff(c_217,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_185,plain,(
    ! [B_22,A_23] :
      ( k9_relat_1(B_22,k2_relat_1(A_23)) = k2_relat_1(k5_relat_1(A_23,B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_194,plain,(
    ! [B_22] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_22)) = k9_relat_1(B_22,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_185])).

tff(c_332,plain,(
    ! [B_28] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_28)) = k9_relat_1(B_28,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_194])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

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

tff(c_82,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_89,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_82])).

tff(c_85,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_91,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_85])).

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

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_134,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_91,c_96])).

tff(c_8,plain,(
    ! [A_6,B_8] :
      ( k10_relat_1(A_6,k1_relat_1(B_8)) = k1_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_8])).

tff(c_145,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_26,c_138])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_145])).

tff(c_148,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_341,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_148])).

tff(c_350,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_341])).

tff(c_354,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_350])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:21:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.07/1.28  
% 2.07/1.28  %Foreground sorts:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Background operators:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Foreground operators:
% 2.07/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.07/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.07/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.07/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.28  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.07/1.28  
% 2.07/1.29  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.07/1.29  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.07/1.29  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.07/1.29  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.07/1.29  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.07/1.29  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.07/1.29  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.07/1.29  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.07/1.29  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.07/1.29  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.29  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.07/1.29  tff(c_18, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.07/1.29  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.07/1.29  tff(c_157, plain, (![A_21]: (k4_relat_1(A_21)=k2_funct_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.29  tff(c_160, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_157])).
% 2.07/1.29  tff(c_163, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_160])).
% 2.07/1.29  tff(c_10, plain, (![A_9]: (k2_relat_1(k4_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.29  tff(c_167, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_163, c_10])).
% 2.07/1.29  tff(c_174, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_167])).
% 2.07/1.29  tff(c_12, plain, (![A_9]: (k1_relat_1(k4_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.29  tff(c_170, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_163, c_12])).
% 2.07/1.29  tff(c_176, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_170])).
% 2.07/1.29  tff(c_203, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_2])).
% 2.07/1.29  tff(c_206, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_203])).
% 2.07/1.29  tff(c_208, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_206])).
% 2.07/1.29  tff(c_211, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_208])).
% 2.07/1.29  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_211])).
% 2.07/1.29  tff(c_217, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_206])).
% 2.07/1.29  tff(c_185, plain, (![B_22, A_23]: (k9_relat_1(B_22, k2_relat_1(A_23))=k2_relat_1(k5_relat_1(A_23, B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.07/1.29  tff(c_194, plain, (![B_22]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_22))=k9_relat_1(B_22, k1_relat_1('#skF_1')) | ~v1_relat_1(B_22) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_174, c_185])).
% 2.07/1.29  tff(c_332, plain, (![B_28]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_28))=k9_relat_1(B_28, k1_relat_1('#skF_1')) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_194])).
% 2.07/1.29  tff(c_20, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.07/1.29  tff(c_71, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.07/1.29  tff(c_72, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.29  tff(c_75, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.07/1.29  tff(c_78, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_75])).
% 2.07/1.29  tff(c_82, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 2.07/1.29  tff(c_89, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_82])).
% 2.07/1.29  tff(c_85, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 2.07/1.29  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_85])).
% 2.07/1.29  tff(c_103, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 2.07/1.29  tff(c_106, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_103])).
% 2.07/1.29  tff(c_123, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.07/1.29  tff(c_126, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_123])).
% 2.07/1.29  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_126])).
% 2.07/1.29  tff(c_132, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_106])).
% 2.07/1.29  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.29  tff(c_96, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 2.07/1.29  tff(c_134, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_91, c_96])).
% 2.07/1.29  tff(c_8, plain, (![A_6, B_8]: (k10_relat_1(A_6, k1_relat_1(B_8))=k1_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.29  tff(c_138, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_8])).
% 2.07/1.29  tff(c_145, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_26, c_138])).
% 2.07/1.29  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_145])).
% 2.07/1.29  tff(c_148, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.07/1.29  tff(c_341, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_148])).
% 2.07/1.29  tff(c_350, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_341])).
% 2.07/1.29  tff(c_354, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2, c_350])).
% 2.07/1.29  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_354])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 0
% 2.07/1.29  #Sup     : 85
% 2.07/1.29  #Fact    : 0
% 2.07/1.29  #Define  : 0
% 2.07/1.29  #Split   : 4
% 2.07/1.29  #Chain   : 0
% 2.07/1.29  #Close   : 0
% 2.07/1.29  
% 2.07/1.29  Ordering : KBO
% 2.07/1.29  
% 2.07/1.29  Simplification rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Subsume      : 2
% 2.07/1.29  #Demod        : 42
% 2.07/1.29  #Tautology    : 45
% 2.07/1.29  #SimpNegUnit  : 1
% 2.07/1.29  #BackRed      : 0
% 2.07/1.29  
% 2.07/1.29  #Partial instantiations: 0
% 2.07/1.29  #Strategies tried      : 1
% 2.07/1.29  
% 2.07/1.29  Timing (in seconds)
% 2.07/1.29  ----------------------
% 2.07/1.29  Preprocessing        : 0.28
% 2.07/1.29  Parsing              : 0.15
% 2.07/1.29  CNF conversion       : 0.02
% 2.07/1.29  Main loop            : 0.21
% 2.07/1.29  Inferencing          : 0.08
% 2.07/1.29  Reduction            : 0.06
% 2.07/1.29  Demodulation         : 0.05
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.03
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.53
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
