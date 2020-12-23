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
% DateTime   : Thu Dec  3 10:03:55 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 185 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 464 expanded)
%              Number of equality atoms :   41 ( 156 expanded)
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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_70,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_26,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_67,plain,(
    ! [A_22] :
      ( k4_relat_1(A_22) = k2_funct_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_73,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_2])).

tff(c_91,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_83])).

tff(c_121,plain,(
    ! [A_26,B_27] :
      ( k10_relat_1(A_26,k1_relat_1(B_27)) = k1_relat_1(k5_relat_1(A_26,B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_89,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_80])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_87,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_77])).

tff(c_4,plain,(
    ! [A_2] :
      ( k10_relat_1(A_2,k2_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_4])).

tff(c_100,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_96])).

tff(c_115,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_100])).

tff(c_127,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_115])).

tff(c_142,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_32,c_127])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_142])).

tff(c_145,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_288,plain,(
    ! [A_36] :
      ( k2_relat_1(k5_relat_1(A_36,k2_funct_1(A_36))) = k1_relat_1(A_36)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_151,plain,(
    ! [A_28] :
      ( k4_relat_1(A_28) = k2_funct_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_154,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_157,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_154])).

tff(c_167,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_175,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_161,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_8])).

tff(c_171,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_161])).

tff(c_12,plain,(
    ! [A_7,B_9] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_7,B_9)),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_184,plain,(
    ! [A_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_7,k2_funct_1('#skF_1'))),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_191,plain,(
    ! [A_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_7,k2_funct_1('#skF_1'))),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_184])).

tff(c_295,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_191])).

tff(c_310,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_32,c_295])).

tff(c_365,plain,(
    ! [B_38,A_39] :
      ( k2_relat_1(k5_relat_1(B_38,A_39)) = k2_relat_1(A_39)
      | ~ r1_tarski(k1_relat_1(A_39),k2_relat_1(B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_380,plain,(
    ! [A_39] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_39)) = k2_relat_1(A_39)
      | ~ r1_tarski(k1_relat_1(A_39),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_365])).

tff(c_432,plain,(
    ! [A_44] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_44)) = k2_relat_1(A_44)
      | ~ r1_tarski(k1_relat_1(A_44),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_380])).

tff(c_435,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_310,c_432])).

tff(c_453,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_435])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.23/1.30  
% 2.23/1.30  %Foreground sorts:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Background operators:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Foreground operators:
% 2.23/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.23/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.23/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.30  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.23/1.30  
% 2.23/1.32  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.23/1.32  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.23/1.32  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.23/1.32  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.23/1.32  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.23/1.32  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.23/1.32  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.23/1.32  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.23/1.32  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.23/1.32  tff(c_26, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.23/1.32  tff(c_66, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.23/1.32  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.23/1.32  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.23/1.32  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.23/1.32  tff(c_67, plain, (![A_22]: (k4_relat_1(A_22)=k2_funct_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.32  tff(c_70, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_67])).
% 2.23/1.32  tff(c_73, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_70])).
% 2.23/1.32  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.32  tff(c_83, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_2])).
% 2.23/1.32  tff(c_91, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_83])).
% 2.23/1.32  tff(c_121, plain, (![A_26, B_27]: (k10_relat_1(A_26, k1_relat_1(B_27))=k1_relat_1(k5_relat_1(A_26, B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.32  tff(c_10, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.32  tff(c_80, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 2.23/1.32  tff(c_89, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_80])).
% 2.23/1.32  tff(c_8, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.32  tff(c_77, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_8])).
% 2.23/1.32  tff(c_87, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_77])).
% 2.23/1.32  tff(c_4, plain, (![A_2]: (k10_relat_1(A_2, k2_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.32  tff(c_96, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_4])).
% 2.23/1.32  tff(c_100, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_96])).
% 2.23/1.32  tff(c_115, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_100])).
% 2.23/1.32  tff(c_127, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_115])).
% 2.23/1.32  tff(c_142, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_32, c_127])).
% 2.23/1.32  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_142])).
% 2.23/1.32  tff(c_145, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.23/1.32  tff(c_288, plain, (![A_36]: (k2_relat_1(k5_relat_1(A_36, k2_funct_1(A_36)))=k1_relat_1(A_36) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.23/1.32  tff(c_151, plain, (![A_28]: (k4_relat_1(A_28)=k2_funct_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.32  tff(c_154, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_151])).
% 2.23/1.32  tff(c_157, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_154])).
% 2.23/1.32  tff(c_167, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 2.23/1.32  tff(c_175, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 2.23/1.32  tff(c_161, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_157, c_8])).
% 2.23/1.32  tff(c_171, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_161])).
% 2.23/1.32  tff(c_12, plain, (![A_7, B_9]: (r1_tarski(k2_relat_1(k5_relat_1(A_7, B_9)), k2_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.32  tff(c_184, plain, (![A_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_7, k2_funct_1('#skF_1'))), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 2.23/1.32  tff(c_191, plain, (![A_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_7, k2_funct_1('#skF_1'))), k1_relat_1('#skF_1')) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_184])).
% 2.23/1.32  tff(c_295, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_288, c_191])).
% 2.23/1.32  tff(c_310, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_32, c_295])).
% 2.23/1.32  tff(c_365, plain, (![B_38, A_39]: (k2_relat_1(k5_relat_1(B_38, A_39))=k2_relat_1(A_39) | ~r1_tarski(k1_relat_1(A_39), k2_relat_1(B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.32  tff(c_380, plain, (![A_39]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_39))=k2_relat_1(A_39) | ~r1_tarski(k1_relat_1(A_39), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_171, c_365])).
% 2.23/1.32  tff(c_432, plain, (![A_44]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_44))=k2_relat_1(A_44) | ~r1_tarski(k1_relat_1(A_44), k1_relat_1('#skF_1')) | ~v1_relat_1(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_380])).
% 2.23/1.32  tff(c_435, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_310, c_432])).
% 2.23/1.32  tff(c_453, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_435])).
% 2.23/1.32  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_453])).
% 2.23/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  Inference rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Ref     : 0
% 2.23/1.32  #Sup     : 106
% 2.23/1.32  #Fact    : 0
% 2.23/1.32  #Define  : 0
% 2.23/1.32  #Split   : 5
% 2.23/1.32  #Chain   : 0
% 2.23/1.32  #Close   : 0
% 2.23/1.32  
% 2.23/1.32  Ordering : KBO
% 2.23/1.32  
% 2.23/1.32  Simplification rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Subsume      : 1
% 2.23/1.32  #Demod        : 58
% 2.23/1.32  #Tautology    : 45
% 2.23/1.32  #SimpNegUnit  : 2
% 2.23/1.32  #BackRed      : 0
% 2.23/1.32  
% 2.23/1.32  #Partial instantiations: 0
% 2.23/1.32  #Strategies tried      : 1
% 2.23/1.32  
% 2.23/1.32  Timing (in seconds)
% 2.23/1.32  ----------------------
% 2.23/1.32  Preprocessing        : 0.30
% 2.23/1.32  Parsing              : 0.17
% 2.23/1.32  CNF conversion       : 0.02
% 2.23/1.32  Main loop            : 0.25
% 2.23/1.32  Inferencing          : 0.10
% 2.23/1.32  Reduction            : 0.07
% 2.23/1.32  Demodulation         : 0.05
% 2.23/1.32  BG Simplification    : 0.02
% 2.23/1.32  Subsumption          : 0.05
% 2.23/1.32  Abstraction          : 0.01
% 2.23/1.32  MUC search           : 0.00
% 2.23/1.32  Cooper               : 0.00
% 2.23/1.32  Total                : 0.58
% 2.23/1.32  Index Insertion      : 0.00
% 2.23/1.32  Index Deletion       : 0.00
% 2.23/1.32  Index Matching       : 0.00
% 2.23/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
