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
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  87 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :  102 ( 223 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,(
    ! [A_15] :
      ( k4_relat_1(A_15) = k2_funct_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_65,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_59])).

tff(c_14,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_14])).

tff(c_82,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_69])).

tff(c_12,plain,(
    ! [A_4] :
      ( v1_funct_1(k4_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,
    ( v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_84,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_88,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_78])).

tff(c_10,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_117,plain,(
    ! [A_19,B_20] :
      ( v2_funct_1(A_19)
      | k2_relat_1(B_20) != k1_relat_1(A_19)
      | ~ v2_funct_1(k5_relat_1(B_20,A_19))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,(
    ! [A_8] :
      ( v2_funct_1(k2_funct_1(A_8))
      | k1_relat_1(k2_funct_1(A_8)) != k2_relat_1(A_8)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_8)))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ v1_funct_1(k2_funct_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_139,plain,(
    ! [A_23] :
      ( v2_funct_1(k2_funct_1(A_23))
      | k1_relat_1(k2_funct_1(A_23)) != k2_relat_1(A_23)
      | ~ v1_funct_1(k2_funct_1(A_23))
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_24,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_145,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_24])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_82,c_84,c_88,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:01:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.20  
% 2.06/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.20  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.06/1.20  
% 2.06/1.20  %Foreground sorts:
% 2.06/1.20  
% 2.06/1.20  
% 2.06/1.20  %Background operators:
% 2.06/1.20  
% 2.06/1.20  
% 2.06/1.20  %Foreground operators:
% 2.06/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.06/1.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.06/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.06/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.06/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.20  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.06/1.20  
% 2.19/1.22  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 2.19/1.22  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.19/1.22  tff(f_53, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.19/1.22  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.19/1.22  tff(f_43, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.19/1.22  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.19/1.22  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 2.19/1.22  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.22  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.22  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.22  tff(c_53, plain, (![A_15]: (k4_relat_1(A_15)=k2_funct_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.22  tff(c_59, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.19/1.22  tff(c_65, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_59])).
% 2.19/1.22  tff(c_14, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.22  tff(c_69, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_14])).
% 2.19/1.22  tff(c_82, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_69])).
% 2.19/1.22  tff(c_12, plain, (![A_4]: (v1_funct_1(k4_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.22  tff(c_72, plain, (v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_12])).
% 2.19/1.22  tff(c_84, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_72])).
% 2.19/1.22  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.22  tff(c_78, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_4])).
% 2.19/1.22  tff(c_88, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_78])).
% 2.19/1.22  tff(c_10, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.22  tff(c_22, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.22  tff(c_117, plain, (![A_19, B_20]: (v2_funct_1(A_19) | k2_relat_1(B_20)!=k1_relat_1(A_19) | ~v2_funct_1(k5_relat_1(B_20, A_19)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.22  tff(c_120, plain, (![A_8]: (v2_funct_1(k2_funct_1(A_8)) | k1_relat_1(k2_funct_1(A_8))!=k2_relat_1(A_8) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_8))) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~v1_funct_1(k2_funct_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_22, c_117])).
% 2.19/1.22  tff(c_139, plain, (![A_23]: (v2_funct_1(k2_funct_1(A_23)) | k1_relat_1(k2_funct_1(A_23))!=k2_relat_1(A_23) | ~v1_funct_1(k2_funct_1(A_23)) | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_120])).
% 2.19/1.22  tff(c_24, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.22  tff(c_145, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_139, c_24])).
% 2.19/1.22  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_82, c_84, c_88, c_145])).
% 2.19/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.22  
% 2.19/1.22  Inference rules
% 2.19/1.22  ----------------------
% 2.19/1.22  #Ref     : 0
% 2.19/1.22  #Sup     : 26
% 2.19/1.22  #Fact    : 0
% 2.19/1.22  #Define  : 0
% 2.19/1.22  #Split   : 0
% 2.19/1.22  #Chain   : 0
% 2.19/1.22  #Close   : 0
% 2.19/1.22  
% 2.19/1.22  Ordering : KBO
% 2.19/1.22  
% 2.19/1.22  Simplification rules
% 2.19/1.22  ----------------------
% 2.19/1.22  #Subsume      : 0
% 2.19/1.22  #Demod        : 21
% 2.19/1.22  #Tautology    : 16
% 2.19/1.22  #SimpNegUnit  : 0
% 2.19/1.22  #BackRed      : 0
% 2.19/1.22  
% 2.19/1.22  #Partial instantiations: 0
% 2.19/1.22  #Strategies tried      : 1
% 2.19/1.22  
% 2.19/1.22  Timing (in seconds)
% 2.19/1.22  ----------------------
% 2.19/1.22  Preprocessing        : 0.29
% 2.19/1.22  Parsing              : 0.15
% 2.19/1.22  CNF conversion       : 0.02
% 2.19/1.22  Main loop            : 0.14
% 2.19/1.22  Inferencing          : 0.06
% 2.19/1.22  Reduction            : 0.05
% 2.19/1.22  Demodulation         : 0.04
% 2.19/1.22  BG Simplification    : 0.01
% 2.19/1.22  Subsumption          : 0.02
% 2.19/1.22  Abstraction          : 0.01
% 2.19/1.22  MUC search           : 0.00
% 2.19/1.22  Cooper               : 0.00
% 2.19/1.22  Total                : 0.46
% 2.19/1.22  Index Insertion      : 0.00
% 2.19/1.22  Index Deletion       : 0.00
% 2.19/1.22  Index Matching       : 0.00
% 2.19/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
