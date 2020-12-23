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
% DateTime   : Thu Dec  3 10:03:58 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 168 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  118 ( 414 expanded)
%              Number of equality atoms :   13 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
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

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ! [A_27] :
      ( k4_relat_1(A_27) = k2_funct_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_106,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_100])).

tff(c_12,plain,(
    ! [A_5] :
      ( k2_relat_1(k4_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_110,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_12])).

tff(c_117,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_110])).

tff(c_70,plain,(
    ! [B_22,A_23] :
      ( v5_relat_1(B_22,A_23)
      | ~ r1_tarski(k2_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [B_22] :
      ( v5_relat_1(B_22,k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_127,plain,
    ( v5_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_78])).

tff(c_138,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_141])).

tff(c_147,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_284,plain,(
    ! [B_40,A_41] :
      ( v2_funct_1(B_40)
      | ~ r1_tarski(k2_relat_1(B_40),k1_relat_1(A_41))
      | ~ v2_funct_1(k5_relat_1(B_40,A_41))
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_290,plain,(
    ! [A_41] :
      ( v2_funct_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(A_41))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'),A_41))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_284])).

tff(c_304,plain,(
    ! [A_41] :
      ( v2_funct_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(A_41))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'),A_41))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_290])).

tff(c_305,plain,(
    ! [A_41] :
      ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(A_41))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'),A_41))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_304])).

tff(c_360,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_363,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_360])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_363])).

tff(c_370,plain,(
    ! [A_46] :
      ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(A_46))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'),A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_380,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_370])).

tff(c_385,plain,(
    ~ v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_380])).

tff(c_388,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1('#skF_1')))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_385])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_24,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.37  
% 2.28/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.38  %$ v5_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.28/1.38  
% 2.28/1.38  %Foreground sorts:
% 2.28/1.38  
% 2.28/1.38  
% 2.28/1.38  %Background operators:
% 2.28/1.38  
% 2.28/1.38  
% 2.28/1.38  %Foreground operators:
% 2.28/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.28/1.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.28/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.38  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.28/1.38  
% 2.28/1.39  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 2.28/1.39  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.28/1.39  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.28/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.39  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.28/1.39  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.28/1.39  tff(f_43, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.28/1.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.28/1.39  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 2.28/1.39  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.28/1.39  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.28/1.39  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.28/1.39  tff(c_24, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.39  tff(c_28, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.28/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.39  tff(c_18, plain, (![A_7]: (v1_funct_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.39  tff(c_32, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.28/1.39  tff(c_20, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.39  tff(c_94, plain, (![A_27]: (k4_relat_1(A_27)=k2_funct_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.39  tff(c_100, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_94])).
% 2.28/1.39  tff(c_106, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_100])).
% 2.28/1.39  tff(c_12, plain, (![A_5]: (k2_relat_1(k4_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.39  tff(c_110, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_106, c_12])).
% 2.28/1.39  tff(c_117, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_110])).
% 2.28/1.39  tff(c_70, plain, (![B_22, A_23]: (v5_relat_1(B_22, A_23) | ~r1_tarski(k2_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.39  tff(c_78, plain, (![B_22]: (v5_relat_1(B_22, k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_6, c_70])).
% 2.28/1.39  tff(c_127, plain, (v5_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_78])).
% 2.28/1.39  tff(c_138, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_127])).
% 2.28/1.39  tff(c_141, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_138])).
% 2.28/1.39  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_141])).
% 2.28/1.39  tff(c_147, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_127])).
% 2.28/1.39  tff(c_284, plain, (![B_40, A_41]: (v2_funct_1(B_40) | ~r1_tarski(k2_relat_1(B_40), k1_relat_1(A_41)) | ~v2_funct_1(k5_relat_1(B_40, A_41)) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.39  tff(c_290, plain, (![A_41]: (v2_funct_1(k2_funct_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(A_41)) | ~v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'), A_41)) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_117, c_284])).
% 2.28/1.39  tff(c_304, plain, (![A_41]: (v2_funct_1(k2_funct_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(A_41)) | ~v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'), A_41)) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_290])).
% 2.28/1.39  tff(c_305, plain, (![A_41]: (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(A_41)) | ~v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'), A_41)) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(negUnitSimplification, [status(thm)], [c_32, c_304])).
% 2.28/1.39  tff(c_360, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_305])).
% 2.28/1.39  tff(c_363, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_360])).
% 2.28/1.39  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_363])).
% 2.28/1.39  tff(c_370, plain, (![A_46]: (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(A_46)) | ~v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'), A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(splitRight, [status(thm)], [c_305])).
% 2.28/1.39  tff(c_380, plain, (~v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_370])).
% 2.28/1.39  tff(c_385, plain, (~v2_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_380])).
% 2.28/1.39  tff(c_388, plain, (~v2_funct_1(k6_relat_1(k2_relat_1('#skF_1'))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_385])).
% 2.28/1.39  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_24, c_388])).
% 2.28/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.39  
% 2.28/1.39  Inference rules
% 2.28/1.39  ----------------------
% 2.28/1.39  #Ref     : 0
% 2.28/1.39  #Sup     : 73
% 2.28/1.39  #Fact    : 0
% 2.28/1.39  #Define  : 0
% 2.28/1.39  #Split   : 3
% 2.28/1.39  #Chain   : 0
% 2.28/1.39  #Close   : 0
% 2.28/1.39  
% 2.28/1.39  Ordering : KBO
% 2.28/1.39  
% 2.28/1.39  Simplification rules
% 2.28/1.39  ----------------------
% 2.28/1.39  #Subsume      : 12
% 2.28/1.39  #Demod        : 66
% 2.28/1.39  #Tautology    : 29
% 2.28/1.39  #SimpNegUnit  : 1
% 2.28/1.39  #BackRed      : 0
% 2.28/1.39  
% 2.28/1.39  #Partial instantiations: 0
% 2.28/1.39  #Strategies tried      : 1
% 2.28/1.39  
% 2.28/1.39  Timing (in seconds)
% 2.28/1.39  ----------------------
% 2.60/1.39  Preprocessing        : 0.33
% 2.60/1.39  Parsing              : 0.17
% 2.60/1.39  CNF conversion       : 0.02
% 2.60/1.39  Main loop            : 0.25
% 2.60/1.39  Inferencing          : 0.09
% 2.60/1.39  Reduction            : 0.08
% 2.60/1.39  Demodulation         : 0.06
% 2.60/1.39  BG Simplification    : 0.01
% 2.60/1.39  Subsumption          : 0.05
% 2.60/1.39  Abstraction          : 0.01
% 2.60/1.40  MUC search           : 0.00
% 2.60/1.40  Cooper               : 0.00
% 2.60/1.40  Total                : 0.60
% 2.60/1.40  Index Insertion      : 0.00
% 2.60/1.40  Index Deletion       : 0.00
% 2.60/1.40  Index Matching       : 0.00
% 2.60/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
