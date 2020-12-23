%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 142 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 334 expanded)
%              Number of equality atoms :   37 ( 120 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_65,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_2] :
      ( k9_relat_1(A_2,k1_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [A_17] :
      ( k4_relat_1(A_17) = k2_funct_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_74,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_71])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_167,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_12,plain,(
    ! [A_10] :
      ( k2_relat_1(k4_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_12])).

tff(c_163,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_153])).

tff(c_198,plain,(
    ! [B_20,A_21] :
      ( k9_relat_1(B_20,k2_relat_1(A_21)) = k2_relat_1(k5_relat_1(A_21,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_213,plain,(
    ! [B_20] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_20)) = k9_relat_1(B_20,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_198])).

tff(c_242,plain,(
    ! [B_22] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_22)) = k9_relat_1(B_22,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_213])).

tff(c_18,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_85,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_93,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_85])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_relat_1(k4_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_91,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_82])).

tff(c_79,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_12])).

tff(c_89,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_79])).

tff(c_8,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_8])).

tff(c_102,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_98])).

tff(c_134,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_102])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( k10_relat_1(A_7,k1_relat_1(B_9)) = k1_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_10])).

tff(c_145,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_24,c_138])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_145])).

tff(c_148,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_251,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_148])).

tff(c_260,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_251])).

tff(c_264,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_260])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.02/1.27  
% 2.02/1.27  %Foreground sorts:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Background operators:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Foreground operators:
% 2.02/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.02/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.02/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.02/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.27  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.02/1.27  
% 2.02/1.28  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.02/1.28  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.02/1.28  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.02/1.28  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.02/1.28  tff(f_57, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.02/1.28  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.02/1.28  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.02/1.28  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.02/1.28  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.28  tff(c_4, plain, (![A_2]: (k9_relat_1(A_2, k1_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.28  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.28  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.28  tff(c_68, plain, (![A_17]: (k4_relat_1(A_17)=k2_funct_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.28  tff(c_71, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_68])).
% 2.02/1.28  tff(c_74, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_71])).
% 2.02/1.28  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.28  tff(c_159, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 2.02/1.28  tff(c_167, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_159])).
% 2.02/1.28  tff(c_12, plain, (![A_10]: (k2_relat_1(k4_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.28  tff(c_153, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_12])).
% 2.02/1.28  tff(c_163, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_153])).
% 2.02/1.28  tff(c_198, plain, (![B_20, A_21]: (k9_relat_1(B_20, k2_relat_1(A_21))=k2_relat_1(k5_relat_1(A_21, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.28  tff(c_213, plain, (![B_20]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_20))=k9_relat_1(B_20, k1_relat_1('#skF_1')) | ~v1_relat_1(B_20) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_198])).
% 2.02/1.28  tff(c_242, plain, (![B_22]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_22))=k9_relat_1(B_22, k1_relat_1('#skF_1')) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_213])).
% 2.02/1.28  tff(c_18, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.28  tff(c_75, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 2.02/1.28  tff(c_85, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 2.02/1.28  tff(c_93, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_85])).
% 2.02/1.28  tff(c_14, plain, (![A_10]: (k1_relat_1(k4_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.28  tff(c_82, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 2.02/1.28  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_82])).
% 2.02/1.28  tff(c_79, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_12])).
% 2.02/1.28  tff(c_89, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_79])).
% 2.02/1.28  tff(c_8, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.28  tff(c_98, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_8])).
% 2.02/1.28  tff(c_102, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_98])).
% 2.02/1.28  tff(c_134, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_102])).
% 2.02/1.28  tff(c_10, plain, (![A_7, B_9]: (k10_relat_1(A_7, k1_relat_1(B_9))=k1_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.28  tff(c_138, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_10])).
% 2.02/1.28  tff(c_145, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_24, c_138])).
% 2.02/1.28  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_145])).
% 2.02/1.28  tff(c_148, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 2.02/1.28  tff(c_251, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_242, c_148])).
% 2.02/1.28  tff(c_260, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_251])).
% 2.02/1.28  tff(c_264, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4, c_260])).
% 2.02/1.28  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_264])).
% 2.02/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  Inference rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Ref     : 0
% 2.02/1.28  #Sup     : 66
% 2.02/1.28  #Fact    : 0
% 2.02/1.28  #Define  : 0
% 2.02/1.28  #Split   : 2
% 2.02/1.28  #Chain   : 0
% 2.02/1.28  #Close   : 0
% 2.02/1.28  
% 2.02/1.28  Ordering : KBO
% 2.02/1.28  
% 2.02/1.28  Simplification rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Subsume      : 0
% 2.02/1.28  #Demod        : 27
% 2.02/1.28  #Tautology    : 38
% 2.02/1.28  #SimpNegUnit  : 1
% 2.02/1.28  #BackRed      : 0
% 2.02/1.28  
% 2.02/1.28  #Partial instantiations: 0
% 2.02/1.28  #Strategies tried      : 1
% 2.02/1.28  
% 2.02/1.28  Timing (in seconds)
% 2.02/1.28  ----------------------
% 2.02/1.29  Preprocessing        : 0.31
% 2.02/1.29  Parsing              : 0.17
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.18
% 2.02/1.29  Inferencing          : 0.07
% 2.02/1.29  Reduction            : 0.05
% 2.02/1.29  Demodulation         : 0.04
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.03
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.29  MUC search           : 0.00
% 2.02/1.29  Cooper               : 0.00
% 2.02/1.29  Total                : 0.52
% 2.02/1.29  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
