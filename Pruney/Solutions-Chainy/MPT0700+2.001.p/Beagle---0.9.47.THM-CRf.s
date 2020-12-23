%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:01 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 256 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 671 expanded)
%              Number of equality atoms :   16 ( 121 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    ! [A_19] :
      ( k4_relat_1(A_19) = k2_funct_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_54,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_50])).

tff(c_6,plain,(
    ! [A_5] :
      ( v1_relat_1(k4_relat_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_67,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_61])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_funct_1(k4_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_65,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_58])).

tff(c_16,plain,(
    ! [A_10] :
      ( v2_funct_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    ! [A_23] :
      ( k4_relat_1(k2_funct_1(A_23)) = k2_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(k2_funct_1(A_23))
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_107,plain,
    ( k4_relat_1(k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_101])).

tff(c_110,plain,(
    k4_relat_1(k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_65,c_107])).

tff(c_114,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_10])).

tff(c_121,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_65,c_114])).

tff(c_136,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_139,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_139])).

tff(c_145,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_funct_1(k2_funct_1(A_11)) = A_11
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_89,plain,(
    ! [B_21,A_22] :
      ( k10_relat_1(k2_funct_1(B_21),A_22) = k9_relat_1(B_21,A_22)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_240,plain,(
    ! [A_24,A_25] :
      ( k9_relat_1(k2_funct_1(A_24),A_25) = k10_relat_1(A_24,A_25)
      | ~ v2_funct_1(k2_funct_1(A_24))
      | ~ v1_funct_1(k2_funct_1(A_24))
      | ~ v1_relat_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_89])).

tff(c_244,plain,(
    ! [A_25] :
      ( k9_relat_1(k2_funct_1('#skF_2'),A_25) = k10_relat_1('#skF_2',A_25)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_145,c_240])).

tff(c_253,plain,(
    ! [A_25] : k9_relat_1(k2_funct_1('#skF_2'),A_25) = k10_relat_1('#skF_2',A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_67,c_65,c_244])).

tff(c_20,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') != k10_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_2 > #skF_1
% 2.09/1.24  
% 2.09/1.24  %Foreground sorts:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Background operators:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Foreground operators:
% 2.09/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.09/1.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.09/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.24  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.09/1.24  
% 2.09/1.26  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 2.09/1.26  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.09/1.26  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.09/1.26  tff(f_53, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.09/1.26  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 2.09/1.26  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 2.09/1.26  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 2.09/1.26  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.09/1.26  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.09/1.26  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.09/1.26  tff(c_44, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.26  tff(c_50, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_44])).
% 2.09/1.26  tff(c_54, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_50])).
% 2.09/1.26  tff(c_6, plain, (![A_5]: (v1_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.26  tff(c_61, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54, c_6])).
% 2.09/1.26  tff(c_67, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_61])).
% 2.09/1.26  tff(c_10, plain, (![A_7]: (v1_funct_1(k4_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.26  tff(c_58, plain, (v1_funct_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54, c_10])).
% 2.09/1.26  tff(c_65, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_58])).
% 2.09/1.26  tff(c_16, plain, (![A_10]: (v2_funct_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.26  tff(c_101, plain, (![A_23]: (k4_relat_1(k2_funct_1(A_23))=k2_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(k2_funct_1(A_23)) | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_16, c_44])).
% 2.09/1.26  tff(c_107, plain, (k4_relat_1(k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_67, c_101])).
% 2.09/1.26  tff(c_110, plain, (k4_relat_1(k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_65, c_107])).
% 2.09/1.26  tff(c_114, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_10])).
% 2.09/1.26  tff(c_121, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_65, c_114])).
% 2.09/1.26  tff(c_136, plain, (~v2_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_121])).
% 2.09/1.26  tff(c_139, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_136])).
% 2.09/1.26  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_139])).
% 2.09/1.26  tff(c_145, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_121])).
% 2.09/1.26  tff(c_18, plain, (![A_11]: (k2_funct_1(k2_funct_1(A_11))=A_11 | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.26  tff(c_89, plain, (![B_21, A_22]: (k10_relat_1(k2_funct_1(B_21), A_22)=k9_relat_1(B_21, A_22) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.26  tff(c_240, plain, (![A_24, A_25]: (k9_relat_1(k2_funct_1(A_24), A_25)=k10_relat_1(A_24, A_25) | ~v2_funct_1(k2_funct_1(A_24)) | ~v1_funct_1(k2_funct_1(A_24)) | ~v1_relat_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_18, c_89])).
% 2.09/1.26  tff(c_244, plain, (![A_25]: (k9_relat_1(k2_funct_1('#skF_2'), A_25)=k10_relat_1('#skF_2', A_25) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_145, c_240])).
% 2.09/1.26  tff(c_253, plain, (![A_25]: (k9_relat_1(k2_funct_1('#skF_2'), A_25)=k10_relat_1('#skF_2', A_25))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_67, c_65, c_244])).
% 2.09/1.26  tff(c_20, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')!=k10_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.09/1.26  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_20])).
% 2.09/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  Inference rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Ref     : 1
% 2.09/1.26  #Sup     : 53
% 2.09/1.26  #Fact    : 0
% 2.09/1.26  #Define  : 0
% 2.09/1.26  #Split   : 1
% 2.09/1.26  #Chain   : 0
% 2.09/1.26  #Close   : 0
% 2.09/1.26  
% 2.09/1.26  Ordering : KBO
% 2.09/1.26  
% 2.09/1.26  Simplification rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Subsume      : 1
% 2.09/1.26  #Demod        : 98
% 2.09/1.26  #Tautology    : 35
% 2.09/1.26  #SimpNegUnit  : 0
% 2.09/1.26  #BackRed      : 3
% 2.09/1.26  
% 2.09/1.26  #Partial instantiations: 0
% 2.09/1.26  #Strategies tried      : 1
% 2.09/1.26  
% 2.09/1.26  Timing (in seconds)
% 2.09/1.26  ----------------------
% 2.09/1.26  Preprocessing        : 0.28
% 2.09/1.26  Parsing              : 0.15
% 2.09/1.26  CNF conversion       : 0.02
% 2.09/1.26  Main loop            : 0.18
% 2.09/1.26  Inferencing          : 0.07
% 2.09/1.26  Reduction            : 0.06
% 2.09/1.26  Demodulation         : 0.04
% 2.09/1.26  BG Simplification    : 0.01
% 2.09/1.26  Subsumption          : 0.03
% 2.09/1.26  Abstraction          : 0.01
% 2.09/1.26  MUC search           : 0.00
% 2.09/1.26  Cooper               : 0.00
% 2.09/1.26  Total                : 0.49
% 2.09/1.26  Index Insertion      : 0.00
% 2.09/1.26  Index Deletion       : 0.00
% 2.09/1.26  Index Matching       : 0.00
% 2.09/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
