%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   42 (  97 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 291 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_52,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_50,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    ! [A_15,B_16] :
      ( v2_funct_1(A_15)
      | k2_relat_1(B_16) != k1_relat_1(A_15)
      | ~ v2_funct_1(k5_relat_1(B_16,A_15))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | k1_relat_1(k2_funct_1(A_7)) != k2_relat_1(A_7)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_7)))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_88,plain,(
    ! [A_19] :
      ( v2_funct_1(k2_funct_1(A_19))
      | k1_relat_1(k2_funct_1(A_19)) != k2_relat_1(A_19)
      | ~ v1_funct_1(k2_funct_1(A_19))
      | ~ v1_relat_1(k2_funct_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_20,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_91,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_20])).

tff(c_94,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_91])).

tff(c_95,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_105,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_95])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_105])).

tff(c_110,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_112,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_115,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_115])).

tff(c_120,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_124,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_120])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.99/1.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.99/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.20  
% 1.99/1.21  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 1.99/1.21  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.99/1.21  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.99/1.21  tff(f_52, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 1.99/1.21  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.99/1.21  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 1.99/1.21  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.99/1.21  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.99/1.21  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.21  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.99/1.21  tff(c_14, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.21  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.21  tff(c_10, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.21  tff(c_18, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.21  tff(c_66, plain, (![A_15, B_16]: (v2_funct_1(A_15) | k2_relat_1(B_16)!=k1_relat_1(A_15) | ~v2_funct_1(k5_relat_1(B_16, A_15)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.21  tff(c_72, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | k1_relat_1(k2_funct_1(A_7))!=k2_relat_1(A_7) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_7))) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_18, c_66])).
% 1.99/1.21  tff(c_88, plain, (![A_19]: (v2_funct_1(k2_funct_1(A_19)) | k1_relat_1(k2_funct_1(A_19))!=k2_relat_1(A_19) | ~v1_funct_1(k2_funct_1(A_19)) | ~v1_relat_1(k2_funct_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 1.99/1.21  tff(c_20, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.99/1.21  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_88, c_20])).
% 1.99/1.21  tff(c_94, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_91])).
% 1.99/1.21  tff(c_95, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_94])).
% 1.99/1.21  tff(c_105, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_95])).
% 1.99/1.21  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_105])).
% 1.99/1.21  tff(c_110, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_94])).
% 1.99/1.21  tff(c_112, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_110])).
% 1.99/1.21  tff(c_115, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_112])).
% 1.99/1.21  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_115])).
% 1.99/1.21  tff(c_120, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_110])).
% 1.99/1.21  tff(c_124, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_120])).
% 1.99/1.21  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_124])).
% 1.99/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  Inference rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Ref     : 0
% 1.99/1.21  #Sup     : 17
% 1.99/1.21  #Fact    : 0
% 1.99/1.21  #Define  : 0
% 1.99/1.21  #Split   : 2
% 1.99/1.21  #Chain   : 0
% 1.99/1.21  #Close   : 0
% 1.99/1.21  
% 1.99/1.21  Ordering : KBO
% 1.99/1.21  
% 1.99/1.21  Simplification rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Subsume      : 0
% 1.99/1.21  #Demod        : 17
% 1.99/1.21  #Tautology    : 10
% 1.99/1.21  #SimpNegUnit  : 0
% 1.99/1.21  #BackRed      : 0
% 1.99/1.21  
% 1.99/1.21  #Partial instantiations: 0
% 1.99/1.21  #Strategies tried      : 1
% 1.99/1.21  
% 1.99/1.21  Timing (in seconds)
% 1.99/1.21  ----------------------
% 1.99/1.21  Preprocessing        : 0.30
% 1.99/1.21  Parsing              : 0.16
% 1.99/1.21  CNF conversion       : 0.02
% 1.99/1.21  Main loop            : 0.14
% 1.99/1.21  Inferencing          : 0.06
% 1.99/1.21  Reduction            : 0.04
% 1.99/1.21  Demodulation         : 0.03
% 1.99/1.21  BG Simplification    : 0.01
% 1.99/1.21  Subsumption          : 0.02
% 1.99/1.21  Abstraction          : 0.01
% 1.99/1.21  MUC search           : 0.00
% 1.99/1.21  Cooper               : 0.00
% 1.99/1.21  Total                : 0.47
% 1.99/1.21  Index Insertion      : 0.00
% 1.99/1.21  Index Deletion       : 0.00
% 1.99/1.21  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
