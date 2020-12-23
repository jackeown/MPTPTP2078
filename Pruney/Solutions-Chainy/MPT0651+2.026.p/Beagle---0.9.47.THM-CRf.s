%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:51 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 141 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 333 expanded)
%              Number of equality atoms :   36 ( 119 expanded)
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
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

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

tff(c_113,plain,(
    ! [A_18,B_19] :
      ( k10_relat_1(A_18,k1_relat_1(B_19)) = k1_relat_1(k5_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_18] :
      ( k1_relat_1(k5_relat_1(A_18,k2_funct_1('#skF_1'))) = k10_relat_1(A_18,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_113])).

tff(c_159,plain,(
    ! [A_20] :
      ( k1_relat_1(k5_relat_1(A_20,k2_funct_1('#skF_1'))) = k10_relat_1(A_20,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_122])).

tff(c_18,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_168,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_75])).

tff(c_177,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_168])).

tff(c_181,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_177])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_181])).

tff(c_186,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_197,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_205,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_197])).

tff(c_308,plain,(
    ! [B_24,A_25] :
      ( k9_relat_1(B_24,k2_relat_1(A_25)) = k2_relat_1(k5_relat_1(A_25,B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_10] :
      ( k2_relat_1(k4_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_191,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_12])).

tff(c_201,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_191])).

tff(c_194,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_203,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_4,plain,(
    ! [A_2] :
      ( k9_relat_1(A_2,k1_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_4])).

tff(c_223,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_201,c_219])).

tff(c_314,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_223])).

tff(c_329,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_205,c_314])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.23  
% 1.85/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.24  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.85/1.24  
% 1.85/1.24  %Foreground sorts:
% 1.85/1.24  
% 1.85/1.24  
% 1.85/1.24  %Background operators:
% 1.85/1.24  
% 1.85/1.24  
% 1.85/1.24  %Foreground operators:
% 1.85/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.85/1.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.85/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.85/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.85/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.24  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.85/1.24  
% 1.85/1.25  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 1.85/1.25  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.85/1.25  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.85/1.25  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.85/1.25  tff(f_57, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.85/1.25  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.85/1.25  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.85/1.25  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.85/1.25  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.85/1.25  tff(c_8, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.25  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.85/1.25  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.85/1.25  tff(c_68, plain, (![A_17]: (k4_relat_1(A_17)=k2_funct_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.25  tff(c_71, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.85/1.25  tff(c_74, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_71])).
% 1.85/1.25  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.25  tff(c_85, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 1.85/1.25  tff(c_93, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_85])).
% 1.85/1.25  tff(c_14, plain, (![A_10]: (k1_relat_1(k4_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.25  tff(c_82, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 1.85/1.25  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_82])).
% 1.85/1.25  tff(c_113, plain, (![A_18, B_19]: (k10_relat_1(A_18, k1_relat_1(B_19))=k1_relat_1(k5_relat_1(A_18, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.25  tff(c_122, plain, (![A_18]: (k1_relat_1(k5_relat_1(A_18, k2_funct_1('#skF_1')))=k10_relat_1(A_18, k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_91, c_113])).
% 1.85/1.25  tff(c_159, plain, (![A_20]: (k1_relat_1(k5_relat_1(A_20, k2_funct_1('#skF_1')))=k10_relat_1(A_20, k2_relat_1('#skF_1')) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_122])).
% 1.85/1.25  tff(c_18, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.85/1.25  tff(c_75, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 1.85/1.25  tff(c_168, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159, c_75])).
% 1.85/1.25  tff(c_177, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_168])).
% 1.85/1.25  tff(c_181, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_177])).
% 1.85/1.25  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_181])).
% 1.85/1.25  tff(c_186, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 1.85/1.25  tff(c_197, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 1.85/1.25  tff(c_205, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_197])).
% 1.85/1.25  tff(c_308, plain, (![B_24, A_25]: (k9_relat_1(B_24, k2_relat_1(A_25))=k2_relat_1(k5_relat_1(A_25, B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.85/1.25  tff(c_12, plain, (![A_10]: (k2_relat_1(k4_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.25  tff(c_191, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_12])).
% 1.85/1.25  tff(c_201, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_191])).
% 1.85/1.25  tff(c_194, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 1.85/1.25  tff(c_203, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 1.85/1.25  tff(c_4, plain, (![A_2]: (k9_relat_1(A_2, k1_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.25  tff(c_219, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_4])).
% 1.85/1.25  tff(c_223, plain, (k9_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_201, c_219])).
% 1.85/1.25  tff(c_314, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_308, c_223])).
% 1.85/1.25  tff(c_329, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_205, c_314])).
% 1.85/1.25  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_329])).
% 1.85/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.25  
% 1.85/1.25  Inference rules
% 1.85/1.25  ----------------------
% 1.85/1.25  #Ref     : 0
% 1.85/1.25  #Sup     : 83
% 1.85/1.25  #Fact    : 0
% 1.85/1.25  #Define  : 0
% 1.85/1.25  #Split   : 2
% 1.85/1.25  #Chain   : 0
% 1.85/1.25  #Close   : 0
% 1.85/1.25  
% 1.85/1.25  Ordering : KBO
% 1.85/1.25  
% 1.85/1.25  Simplification rules
% 1.85/1.25  ----------------------
% 1.85/1.25  #Subsume      : 1
% 1.85/1.25  #Demod        : 33
% 1.85/1.25  #Tautology    : 44
% 1.85/1.25  #SimpNegUnit  : 1
% 1.85/1.25  #BackRed      : 0
% 1.85/1.25  
% 1.85/1.25  #Partial instantiations: 0
% 1.85/1.25  #Strategies tried      : 1
% 1.85/1.25  
% 1.85/1.25  Timing (in seconds)
% 1.85/1.25  ----------------------
% 1.85/1.25  Preprocessing        : 0.28
% 1.85/1.25  Parsing              : 0.15
% 1.85/1.25  CNF conversion       : 0.02
% 1.85/1.25  Main loop            : 0.19
% 1.85/1.25  Inferencing          : 0.08
% 1.85/1.25  Reduction            : 0.06
% 1.85/1.25  Demodulation         : 0.04
% 1.85/1.25  BG Simplification    : 0.01
% 1.85/1.25  Subsumption          : 0.03
% 1.85/1.25  Abstraction          : 0.01
% 1.85/1.25  MUC search           : 0.00
% 1.85/1.25  Cooper               : 0.00
% 1.85/1.25  Total                : 0.50
% 1.85/1.25  Index Insertion      : 0.00
% 1.85/1.25  Index Deletion       : 0.00
% 1.85/1.25  Index Matching       : 0.00
% 1.85/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
