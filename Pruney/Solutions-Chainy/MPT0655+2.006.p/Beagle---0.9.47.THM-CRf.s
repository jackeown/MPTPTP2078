%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 246 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 699 expanded)
%              Number of equality atoms :   22 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_45,plain,(
    ! [A_12] :
      ( k4_relat_1(A_12) = k2_funct_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_45])).

tff(c_51,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_15,B_16] :
      ( v2_funct_1(A_15)
      | k6_relat_1(k1_relat_1(A_15)) != k5_relat_1(A_15,B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [A_17,B_18] :
      ( v2_funct_1(k4_relat_1(A_17))
      | k5_relat_1(k4_relat_1(A_17),B_18) != k6_relat_1(k2_relat_1(A_17))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k4_relat_1(A_17))
      | ~ v1_relat_1(k4_relat_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_108,plain,(
    ! [B_18] :
      ( v2_funct_1(k4_relat_1('#skF_1'))
      | k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k4_relat_1('#skF_1'))
      | ~ v1_relat_1(k4_relat_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_103])).

tff(c_110,plain,(
    ! [B_18] :
      ( v2_funct_1(k2_funct_1('#skF_1'))
      | k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_51,c_51,c_51,c_108])).

tff(c_111,plain,(
    ! [B_18] :
      ( k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_110])).

tff(c_112,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_115,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_115])).

tff(c_121,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_55,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_4])).

tff(c_62,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_55])).

tff(c_98,plain,(
    ! [B_16] :
      ( v2_funct_1(k2_funct_1('#skF_1'))
      | k5_relat_1(k2_funct_1('#skF_1'),B_16) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_92])).

tff(c_102,plain,(
    ! [B_16] :
      ( k5_relat_1(k2_funct_1('#skF_1'),B_16) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_98])).

tff(c_123,plain,(
    ! [B_16] :
      ( k5_relat_1(k2_funct_1('#skF_1'),B_16) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_102])).

tff(c_124,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_127,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_127])).

tff(c_134,plain,(
    ! [B_19] :
      ( k5_relat_1(k2_funct_1('#skF_1'),B_19) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_138,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.30  
% 1.85/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.30  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.85/1.30  
% 1.85/1.30  %Foreground sorts:
% 1.85/1.30  
% 1.85/1.30  
% 1.85/1.30  %Background operators:
% 1.85/1.30  
% 1.85/1.30  
% 1.85/1.30  %Foreground operators:
% 1.85/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.85/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.85/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.85/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.85/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.30  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.85/1.30  
% 1.85/1.31  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 1.85/1.31  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.85/1.31  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.85/1.31  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.85/1.31  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.85/1.31  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 1.85/1.31  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.31  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.31  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.31  tff(c_14, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.85/1.31  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.31  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.31  tff(c_18, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.31  tff(c_45, plain, (![A_12]: (k4_relat_1(A_12)=k2_funct_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.31  tff(c_48, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_45])).
% 1.85/1.31  tff(c_51, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_48])).
% 1.85/1.31  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.31  tff(c_92, plain, (![A_15, B_16]: (v2_funct_1(A_15) | k6_relat_1(k1_relat_1(A_15))!=k5_relat_1(A_15, B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.31  tff(c_103, plain, (![A_17, B_18]: (v2_funct_1(k4_relat_1(A_17)) | k5_relat_1(k4_relat_1(A_17), B_18)!=k6_relat_1(k2_relat_1(A_17)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k4_relat_1(A_17)) | ~v1_relat_1(k4_relat_1(A_17)) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 1.85/1.31  tff(c_108, plain, (![B_18]: (v2_funct_1(k4_relat_1('#skF_1')) | k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k4_relat_1('#skF_1')) | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_103])).
% 1.85/1.31  tff(c_110, plain, (![B_18]: (v2_funct_1(k2_funct_1('#skF_1')) | k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_51, c_51, c_51, c_108])).
% 1.85/1.31  tff(c_111, plain, (![B_18]: (k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_18, c_110])).
% 1.85/1.31  tff(c_112, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_111])).
% 1.85/1.31  tff(c_115, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_112])).
% 1.85/1.31  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_115])).
% 1.85/1.31  tff(c_121, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_111])).
% 1.85/1.31  tff(c_55, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_51, c_4])).
% 1.85/1.31  tff(c_62, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_55])).
% 1.85/1.31  tff(c_98, plain, (![B_16]: (v2_funct_1(k2_funct_1('#skF_1')) | k5_relat_1(k2_funct_1('#skF_1'), B_16)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_92])).
% 1.85/1.31  tff(c_102, plain, (![B_16]: (k5_relat_1(k2_funct_1('#skF_1'), B_16)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_18, c_98])).
% 1.85/1.31  tff(c_123, plain, (![B_16]: (k5_relat_1(k2_funct_1('#skF_1'), B_16)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_102])).
% 1.85/1.31  tff(c_124, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_123])).
% 1.85/1.31  tff(c_127, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_124])).
% 1.85/1.31  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_127])).
% 1.85/1.31  tff(c_134, plain, (![B_19]: (k5_relat_1(k2_funct_1('#skF_1'), B_19)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(splitRight, [status(thm)], [c_123])).
% 1.85/1.31  tff(c_138, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_134])).
% 1.85/1.31  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_138])).
% 1.85/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.31  
% 1.85/1.31  Inference rules
% 1.85/1.31  ----------------------
% 1.85/1.31  #Ref     : 0
% 1.85/1.31  #Sup     : 27
% 1.85/1.31  #Fact    : 0
% 1.85/1.31  #Define  : 0
% 1.85/1.31  #Split   : 2
% 1.85/1.31  #Chain   : 0
% 1.85/1.31  #Close   : 0
% 1.85/1.31  
% 1.85/1.31  Ordering : KBO
% 1.85/1.31  
% 1.85/1.31  Simplification rules
% 1.85/1.31  ----------------------
% 1.85/1.31  #Subsume      : 0
% 1.85/1.31  #Demod        : 16
% 1.85/1.31  #Tautology    : 16
% 1.85/1.31  #SimpNegUnit  : 2
% 1.85/1.31  #BackRed      : 0
% 1.85/1.31  
% 1.85/1.31  #Partial instantiations: 0
% 1.85/1.31  #Strategies tried      : 1
% 1.85/1.31  
% 1.85/1.31  Timing (in seconds)
% 1.85/1.31  ----------------------
% 1.85/1.31  Preprocessing        : 0.31
% 1.85/1.31  Parsing              : 0.17
% 1.85/1.31  CNF conversion       : 0.02
% 1.85/1.31  Main loop            : 0.14
% 1.85/1.31  Inferencing          : 0.06
% 1.85/1.31  Reduction            : 0.04
% 1.85/1.32  Demodulation         : 0.03
% 1.85/1.32  BG Simplification    : 0.01
% 1.85/1.32  Subsumption          : 0.02
% 1.85/1.32  Abstraction          : 0.01
% 1.85/1.32  MUC search           : 0.00
% 1.85/1.32  Cooper               : 0.00
% 1.85/1.32  Total                : 0.48
% 1.85/1.32  Index Insertion      : 0.00
% 1.85/1.32  Index Deletion       : 0.00
% 1.85/1.32  Index Matching       : 0.00
% 1.85/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
