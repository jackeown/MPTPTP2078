%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:52 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 125 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 295 expanded)
%              Number of equality atoms :   38 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_4] :
      ( k9_relat_1(A_4,k1_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_298,plain,(
    ! [A_29] :
      ( k4_relat_1(A_29) = k2_funct_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_301,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_298])).

tff(c_304,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_301])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_326,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_8])).

tff(c_334,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_326])).

tff(c_14,plain,(
    ! [A_8] :
      ( k2_relat_1(k4_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_323,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_14])).

tff(c_332,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_323])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_339,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_7)) = k9_relat_1(B_7,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_12])).

tff(c_400,plain,(
    ! [B_34] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_34)) = k9_relat_1(B_34,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_339])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_20] :
      ( k4_relat_1(A_20) = k2_funct_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_73,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_76,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_73])).

tff(c_86,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_94,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_86])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(k4_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_90,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_80])).

tff(c_83,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_92,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_83])).

tff(c_205,plain,(
    ! [A_25,B_26] :
      ( k1_relat_1(k5_relat_1(A_25,B_26)) = k1_relat_1(A_25)
      | ~ r1_tarski(k2_relat_1(A_25),k1_relat_1(B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_217,plain,(
    ! [B_26] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_26)) = k1_relat_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_205])).

tff(c_266,plain,(
    ! [B_28] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_28)) = k2_relat_1('#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_217])).

tff(c_279,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_286,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_279])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_286])).

tff(c_289,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_412,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_289])).

tff(c_418,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_412])).

tff(c_422,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_418])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.14/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.14/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.28  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.14/1.28  
% 2.14/1.29  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.14/1.29  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.14/1.29  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.14/1.29  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.14/1.29  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.14/1.29  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.14/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.29  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.14/1.29  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.14/1.29  tff(c_10, plain, (![A_4]: (k9_relat_1(A_4, k1_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.29  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.14/1.29  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.14/1.29  tff(c_298, plain, (![A_29]: (k4_relat_1(A_29)=k2_funct_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.29  tff(c_301, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_298])).
% 2.14/1.29  tff(c_304, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_301])).
% 2.14/1.29  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.29  tff(c_326, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_304, c_8])).
% 2.14/1.29  tff(c_334, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_326])).
% 2.14/1.29  tff(c_14, plain, (![A_8]: (k2_relat_1(k4_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.29  tff(c_323, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_304, c_14])).
% 2.14/1.29  tff(c_332, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_323])).
% 2.14/1.29  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.29  tff(c_339, plain, (![B_7]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_7))=k9_relat_1(B_7, k1_relat_1('#skF_1')) | ~v1_relat_1(B_7) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_332, c_12])).
% 2.14/1.29  tff(c_400, plain, (![B_34]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_34))=k9_relat_1(B_34, k1_relat_1('#skF_1')) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_339])).
% 2.14/1.29  tff(c_22, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.14/1.29  tff(c_69, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.14/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.29  tff(c_70, plain, (![A_20]: (k4_relat_1(A_20)=k2_funct_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.29  tff(c_73, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_70])).
% 2.14/1.29  tff(c_76, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_73])).
% 2.14/1.29  tff(c_86, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 2.14/1.29  tff(c_94, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86])).
% 2.14/1.29  tff(c_16, plain, (![A_8]: (k1_relat_1(k4_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.29  tff(c_80, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_16])).
% 2.14/1.29  tff(c_90, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_80])).
% 2.14/1.29  tff(c_83, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_14])).
% 2.14/1.29  tff(c_92, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_83])).
% 2.14/1.29  tff(c_205, plain, (![A_25, B_26]: (k1_relat_1(k5_relat_1(A_25, B_26))=k1_relat_1(A_25) | ~r1_tarski(k2_relat_1(A_25), k1_relat_1(B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.29  tff(c_217, plain, (![B_26]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_26))=k1_relat_1(k2_funct_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_205])).
% 2.14/1.29  tff(c_266, plain, (![B_28]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_28))=k2_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_217])).
% 2.14/1.29  tff(c_279, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_266])).
% 2.14/1.29  tff(c_286, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_279])).
% 2.14/1.29  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_286])).
% 2.14/1.29  tff(c_289, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.14/1.29  tff(c_412, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_400, c_289])).
% 2.14/1.29  tff(c_418, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_412])).
% 2.14/1.29  tff(c_422, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_418])).
% 2.14/1.29  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_422])).
% 2.14/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  Inference rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Ref     : 0
% 2.14/1.29  #Sup     : 101
% 2.14/1.29  #Fact    : 0
% 2.14/1.29  #Define  : 0
% 2.14/1.29  #Split   : 4
% 2.14/1.29  #Chain   : 0
% 2.14/1.29  #Close   : 0
% 2.14/1.29  
% 2.14/1.29  Ordering : KBO
% 2.14/1.29  
% 2.14/1.29  Simplification rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Subsume      : 2
% 2.14/1.29  #Demod        : 51
% 2.14/1.29  #Tautology    : 47
% 2.14/1.29  #SimpNegUnit  : 1
% 2.14/1.29  #BackRed      : 0
% 2.14/1.29  
% 2.14/1.29  #Partial instantiations: 0
% 2.14/1.29  #Strategies tried      : 1
% 2.14/1.29  
% 2.14/1.29  Timing (in seconds)
% 2.14/1.29  ----------------------
% 2.14/1.29  Preprocessing        : 0.29
% 2.14/1.29  Parsing              : 0.15
% 2.14/1.29  CNF conversion       : 0.02
% 2.14/1.29  Main loop            : 0.24
% 2.14/1.29  Inferencing          : 0.09
% 2.14/1.29  Reduction            : 0.07
% 2.14/1.29  Demodulation         : 0.05
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.05
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.55
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
