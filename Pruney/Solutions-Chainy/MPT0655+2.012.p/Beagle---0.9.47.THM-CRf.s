%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 135 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 442 expanded)
%              Number of equality atoms :   20 (  51 expanded)
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

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    ! [B_16,A_17] :
      ( v2_funct_1(B_16)
      | k2_relat_1(B_16) != k1_relat_1(A_17)
      | ~ v2_funct_1(k5_relat_1(B_16,A_17))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | k2_relat_1(k2_funct_1(A_7)) != k1_relat_1(A_7)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_7)))
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_69])).

tff(c_91,plain,(
    ! [A_20] :
      ( v2_funct_1(k2_funct_1(A_20))
      | k2_relat_1(k2_funct_1(A_20)) != k1_relat_1(A_20)
      | ~ v1_funct_1(k2_funct_1(A_20))
      | ~ v1_relat_1(k2_funct_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_22,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_91,c_22])).

tff(c_97,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_94])).

tff(c_105,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_108,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_108])).

tff(c_114,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_20,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,(
    ! [A_18,B_19] :
      ( v2_funct_1(A_18)
      | k2_relat_1(B_19) != k1_relat_1(A_18)
      | ~ v2_funct_1(k5_relat_1(B_19,A_18))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_20,c_80])).

tff(c_98,plain,(
    ! [A_21] :
      ( v2_funct_1(k2_funct_1(A_21))
      | k1_relat_1(k2_funct_1(A_21)) != k2_relat_1(A_21)
      | ~ v1_funct_1(k2_funct_1(A_21))
      | ~ v1_relat_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_101,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_22])).

tff(c_104,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_101])).

tff(c_116,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_104])).

tff(c_117,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_120,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_120])).

tff(c_125,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_129,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_125])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.29  
% 1.88/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.29  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.88/1.29  
% 1.88/1.29  %Foreground sorts:
% 1.88/1.29  
% 1.88/1.29  
% 1.88/1.29  %Background operators:
% 1.88/1.29  
% 1.88/1.29  
% 1.88/1.29  %Foreground operators:
% 1.88/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.88/1.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.88/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.88/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.88/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.29  
% 2.04/1.30  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 2.04/1.30  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.04/1.30  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.04/1.30  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.04/1.30  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.04/1.30  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 2.04/1.30  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.30  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.30  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.30  tff(c_16, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.30  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.30  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.30  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.30  tff(c_18, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.30  tff(c_69, plain, (![B_16, A_17]: (v2_funct_1(B_16) | k2_relat_1(B_16)!=k1_relat_1(A_17) | ~v2_funct_1(k5_relat_1(B_16, A_17)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.30  tff(c_72, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | k2_relat_1(k2_funct_1(A_7))!=k1_relat_1(A_7) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_7))) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_18, c_69])).
% 2.04/1.30  tff(c_91, plain, (![A_20]: (v2_funct_1(k2_funct_1(A_20)) | k2_relat_1(k2_funct_1(A_20))!=k1_relat_1(A_20) | ~v1_funct_1(k2_funct_1(A_20)) | ~v1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_72])).
% 2.04/1.30  tff(c_22, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.30  tff(c_94, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_91, c_22])).
% 2.04/1.30  tff(c_97, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_94])).
% 2.04/1.30  tff(c_105, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_97])).
% 2.04/1.30  tff(c_108, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_105])).
% 2.04/1.30  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_108])).
% 2.04/1.30  tff(c_114, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_97])).
% 2.04/1.30  tff(c_20, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.30  tff(c_80, plain, (![A_18, B_19]: (v2_funct_1(A_18) | k2_relat_1(B_19)!=k1_relat_1(A_18) | ~v2_funct_1(k5_relat_1(B_19, A_18)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.30  tff(c_86, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | k1_relat_1(k2_funct_1(A_7))!=k2_relat_1(A_7) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_7))) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_80])).
% 2.04/1.30  tff(c_98, plain, (![A_21]: (v2_funct_1(k2_funct_1(A_21)) | k1_relat_1(k2_funct_1(A_21))!=k2_relat_1(A_21) | ~v1_funct_1(k2_funct_1(A_21)) | ~v1_relat_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_86])).
% 2.04/1.30  tff(c_101, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_98, c_22])).
% 2.04/1.30  tff(c_104, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_101])).
% 2.04/1.30  tff(c_116, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_104])).
% 2.04/1.30  tff(c_117, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_116])).
% 2.04/1.30  tff(c_120, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_117])).
% 2.04/1.30  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_120])).
% 2.04/1.30  tff(c_125, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 2.04/1.30  tff(c_129, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_125])).
% 2.04/1.30  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_129])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 17
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 2
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 0
% 2.04/1.30  #Demod        : 18
% 2.04/1.30  #Tautology    : 10
% 2.04/1.30  #SimpNegUnit  : 0
% 2.04/1.30  #BackRed      : 0
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.31  Preprocessing        : 0.30
% 2.04/1.31  Parsing              : 0.16
% 2.04/1.31  CNF conversion       : 0.02
% 2.04/1.31  Main loop            : 0.15
% 2.04/1.31  Inferencing          : 0.06
% 2.04/1.31  Reduction            : 0.04
% 2.04/1.31  Demodulation         : 0.03
% 2.04/1.31  BG Simplification    : 0.01
% 2.04/1.31  Subsumption          : 0.02
% 2.04/1.31  Abstraction          : 0.01
% 2.04/1.31  MUC search           : 0.00
% 2.04/1.31  Cooper               : 0.00
% 2.04/1.31  Total                : 0.48
% 2.04/1.31  Index Insertion      : 0.00
% 2.04/1.31  Index Deletion       : 0.00
% 2.04/1.31  Index Matching       : 0.00
% 2.04/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
