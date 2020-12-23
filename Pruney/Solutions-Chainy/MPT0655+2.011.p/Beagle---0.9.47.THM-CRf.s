%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   50 (  92 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 294 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( k10_relat_1(A_2,k1_relat_1(B_4)) = k1_relat_1(k5_relat_1(A_2,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_26] :
      ( k10_relat_1(k2_funct_1(A_26),k1_relat_1(A_26)) = k1_relat_1(k2_funct_1(A_26))
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_110,plain,(
    ! [B_4] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(B_4),B_4)) = k1_relat_1(k2_funct_1(B_4))
      | ~ v1_relat_1(k2_funct_1(B_4))
      | ~ v2_funct_1(B_4)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(k2_funct_1(B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_12,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_relat_1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_123,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k2_relat_1(B_29),k1_relat_1(A_30))
      | k1_relat_1(k5_relat_1(B_29,A_30)) != k1_relat_1(B_29)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_12,A_10] :
      ( v2_funct_1(B_12)
      | ~ r1_tarski(k2_relat_1(B_12),k1_relat_1(A_10))
      | ~ v2_funct_1(k5_relat_1(B_12,A_10))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,(
    ! [B_33,A_34] :
      ( v2_funct_1(B_33)
      | ~ v2_funct_1(k5_relat_1(B_33,A_34))
      | k1_relat_1(k5_relat_1(B_33,A_34)) != k1_relat_1(B_33)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_123,c_16])).

tff(c_168,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_14)))
      | k1_relat_1(k5_relat_1(k2_funct_1(A_14),A_14)) != k1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_162])).

tff(c_205,plain,(
    ! [A_36] :
      ( v2_funct_1(k2_funct_1(A_36))
      | k1_relat_1(k5_relat_1(k2_funct_1(A_36),A_36)) != k1_relat_1(k2_funct_1(A_36))
      | ~ v1_funct_1(k2_funct_1(A_36))
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_168])).

tff(c_217,plain,(
    ! [B_37] :
      ( v2_funct_1(k2_funct_1(B_37))
      | ~ v1_funct_1(k2_funct_1(B_37))
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k2_funct_1(B_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_205])).

tff(c_26,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_220,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_217,c_26])).

tff(c_223,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_220])).

tff(c_224,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_227,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_227])).

tff(c_232,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_243,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_232])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.27  
% 2.25/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.27  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.25/1.27  
% 2.25/1.27  %Foreground sorts:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Background operators:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Foreground operators:
% 2.25/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.25/1.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.25/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.27  
% 2.25/1.28  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 2.25/1.28  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.25/1.28  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.25/1.28  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.25/1.28  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.25/1.28  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.25/1.28  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.25/1.28  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 2.25/1.28  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 2.25/1.28  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.25/1.28  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.25/1.28  tff(c_6, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.28  tff(c_8, plain, (![A_5]: (v1_relat_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.28  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.25/1.28  tff(c_4, plain, (![A_2, B_4]: (k10_relat_1(A_2, k1_relat_1(B_4))=k1_relat_1(k5_relat_1(A_2, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.25/1.28  tff(c_55, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.28  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.29  tff(c_97, plain, (![A_26]: (k10_relat_1(k2_funct_1(A_26), k1_relat_1(A_26))=k1_relat_1(k2_funct_1(A_26)) | ~v1_relat_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 2.25/1.29  tff(c_110, plain, (![B_4]: (k1_relat_1(k5_relat_1(k2_funct_1(B_4), B_4))=k1_relat_1(k2_funct_1(B_4)) | ~v1_relat_1(k2_funct_1(B_4)) | ~v2_funct_1(B_4) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(k2_funct_1(B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_97])).
% 2.25/1.29  tff(c_12, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.29  tff(c_22, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_relat_1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.25/1.29  tff(c_123, plain, (![B_29, A_30]: (r1_tarski(k2_relat_1(B_29), k1_relat_1(A_30)) | k1_relat_1(k5_relat_1(B_29, A_30))!=k1_relat_1(B_29) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.25/1.29  tff(c_16, plain, (![B_12, A_10]: (v2_funct_1(B_12) | ~r1_tarski(k2_relat_1(B_12), k1_relat_1(A_10)) | ~v2_funct_1(k5_relat_1(B_12, A_10)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.25/1.29  tff(c_162, plain, (![B_33, A_34]: (v2_funct_1(B_33) | ~v2_funct_1(k5_relat_1(B_33, A_34)) | k1_relat_1(k5_relat_1(B_33, A_34))!=k1_relat_1(B_33) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_123, c_16])).
% 2.25/1.29  tff(c_168, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_14))) | k1_relat_1(k5_relat_1(k2_funct_1(A_14), A_14))!=k1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_22, c_162])).
% 2.25/1.29  tff(c_205, plain, (![A_36]: (v2_funct_1(k2_funct_1(A_36)) | k1_relat_1(k5_relat_1(k2_funct_1(A_36), A_36))!=k1_relat_1(k2_funct_1(A_36)) | ~v1_funct_1(k2_funct_1(A_36)) | ~v1_relat_1(k2_funct_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_168])).
% 2.25/1.29  tff(c_217, plain, (![B_37]: (v2_funct_1(k2_funct_1(B_37)) | ~v1_funct_1(k2_funct_1(B_37)) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_relat_1(k2_funct_1(B_37)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_205])).
% 2.25/1.29  tff(c_26, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.25/1.29  tff(c_220, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_217, c_26])).
% 2.25/1.29  tff(c_223, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_220])).
% 2.25/1.29  tff(c_224, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_223])).
% 2.25/1.29  tff(c_227, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_224])).
% 2.25/1.29  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_227])).
% 2.25/1.29  tff(c_232, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_223])).
% 2.25/1.29  tff(c_243, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_232])).
% 2.25/1.29  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_243])).
% 2.25/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  Inference rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Ref     : 0
% 2.25/1.29  #Sup     : 51
% 2.25/1.29  #Fact    : 0
% 2.25/1.29  #Define  : 0
% 2.25/1.29  #Split   : 1
% 2.25/1.29  #Chain   : 0
% 2.25/1.29  #Close   : 0
% 2.25/1.29  
% 2.25/1.29  Ordering : KBO
% 2.25/1.29  
% 2.25/1.29  Simplification rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Subsume      : 3
% 2.25/1.29  #Demod        : 9
% 2.25/1.29  #Tautology    : 19
% 2.25/1.29  #SimpNegUnit  : 0
% 2.25/1.29  #BackRed      : 0
% 2.25/1.29  
% 2.25/1.29  #Partial instantiations: 0
% 2.25/1.29  #Strategies tried      : 1
% 2.25/1.29  
% 2.25/1.29  Timing (in seconds)
% 2.25/1.29  ----------------------
% 2.25/1.29  Preprocessing        : 0.31
% 2.25/1.29  Parsing              : 0.17
% 2.25/1.29  CNF conversion       : 0.02
% 2.25/1.29  Main loop            : 0.22
% 2.25/1.29  Inferencing          : 0.09
% 2.25/1.29  Reduction            : 0.06
% 2.25/1.29  Demodulation         : 0.05
% 2.25/1.29  BG Simplification    : 0.02
% 2.25/1.29  Subsumption          : 0.04
% 2.25/1.29  Abstraction          : 0.01
% 2.25/1.29  MUC search           : 0.00
% 2.25/1.29  Cooper               : 0.00
% 2.25/1.29  Total                : 0.56
% 2.25/1.29  Index Insertion      : 0.00
% 2.25/1.29  Index Deletion       : 0.00
% 2.25/1.29  Index Matching       : 0.00
% 2.25/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
