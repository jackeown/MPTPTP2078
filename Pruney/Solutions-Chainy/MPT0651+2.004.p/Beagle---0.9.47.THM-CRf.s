%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:48 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
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
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_4] :
      ( k10_relat_1(A_4,k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

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

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

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

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( k10_relat_1(A_5,k1_relat_1(B_7)) = k1_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [A_5] :
      ( k1_relat_1(k5_relat_1(A_5,k2_funct_1('#skF_1'))) = k10_relat_1(A_5,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_148,plain,(
    ! [A_23] :
      ( k1_relat_1(k5_relat_1(A_23,k2_funct_1('#skF_1'))) = k10_relat_1(A_23,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_120])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_157,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_69])).

tff(c_163,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_157])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_163])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_167])).

tff(c_172,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [A_24] :
      ( k4_relat_1(A_24) = k2_funct_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_181,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_178])).

tff(c_184,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_181])).

tff(c_194,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_8])).

tff(c_202,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_194])).

tff(c_14,plain,(
    ! [A_8] :
      ( k2_relat_1(k4_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_14])).

tff(c_200,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191])).

tff(c_188,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_16])).

tff(c_198,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_188])).

tff(c_282,plain,(
    ! [B_28,A_29] :
      ( k2_relat_1(k5_relat_1(B_28,A_29)) = k2_relat_1(A_29)
      | ~ r1_tarski(k1_relat_1(A_29),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_294,plain,(
    ! [B_28] :
      ( k2_relat_1(k5_relat_1(B_28,k2_funct_1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_282])).

tff(c_442,plain,(
    ! [B_34] :
      ( k2_relat_1(k5_relat_1(B_34,k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
      | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_200,c_294])).

tff(c_455,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_442])).

tff(c_462,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_455])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.35  
% 2.33/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.35  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.33/1.35  
% 2.33/1.35  %Foreground sorts:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Background operators:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Foreground operators:
% 2.33/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.33/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.33/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.35  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.33/1.35  
% 2.33/1.36  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.33/1.36  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.33/1.36  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.33/1.36  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.33/1.36  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.33/1.36  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.33/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.36  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.33/1.36  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.36  tff(c_10, plain, (![A_4]: (k10_relat_1(A_4, k2_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.36  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.36  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.36  tff(c_70, plain, (![A_20]: (k4_relat_1(A_20)=k2_funct_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.36  tff(c_73, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_70])).
% 2.33/1.36  tff(c_76, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_73])).
% 2.33/1.36  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.36  tff(c_86, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 2.33/1.36  tff(c_94, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86])).
% 2.33/1.36  tff(c_16, plain, (![A_8]: (k1_relat_1(k4_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.37  tff(c_80, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_16])).
% 2.33/1.37  tff(c_90, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_80])).
% 2.33/1.37  tff(c_12, plain, (![A_5, B_7]: (k10_relat_1(A_5, k1_relat_1(B_7))=k1_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.37  tff(c_120, plain, (![A_5]: (k1_relat_1(k5_relat_1(A_5, k2_funct_1('#skF_1')))=k10_relat_1(A_5, k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_90, c_12])).
% 2.33/1.37  tff(c_148, plain, (![A_23]: (k1_relat_1(k5_relat_1(A_23, k2_funct_1('#skF_1')))=k10_relat_1(A_23, k2_relat_1('#skF_1')) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_120])).
% 2.33/1.37  tff(c_22, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.37  tff(c_69, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.33/1.37  tff(c_157, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_148, c_69])).
% 2.33/1.37  tff(c_163, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_157])).
% 2.33/1.37  tff(c_167, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_163])).
% 2.33/1.37  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_167])).
% 2.33/1.37  tff(c_172, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.33/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.37  tff(c_178, plain, (![A_24]: (k4_relat_1(A_24)=k2_funct_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.37  tff(c_181, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_178])).
% 2.33/1.37  tff(c_184, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_181])).
% 2.33/1.37  tff(c_194, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_8])).
% 2.33/1.37  tff(c_202, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_194])).
% 2.33/1.37  tff(c_14, plain, (![A_8]: (k2_relat_1(k4_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.37  tff(c_191, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_14])).
% 2.33/1.37  tff(c_200, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_191])).
% 2.33/1.37  tff(c_188, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_16])).
% 2.33/1.37  tff(c_198, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_188])).
% 2.33/1.37  tff(c_282, plain, (![B_28, A_29]: (k2_relat_1(k5_relat_1(B_28, A_29))=k2_relat_1(A_29) | ~r1_tarski(k1_relat_1(A_29), k2_relat_1(B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.37  tff(c_294, plain, (![B_28]: (k2_relat_1(k5_relat_1(B_28, k2_funct_1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_1')) | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_198, c_282])).
% 2.33/1.37  tff(c_442, plain, (![B_34]: (k2_relat_1(k5_relat_1(B_34, k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_200, c_294])).
% 2.33/1.37  tff(c_455, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_442])).
% 2.33/1.37  tff(c_462, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_455])).
% 2.33/1.37  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_462])).
% 2.33/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.37  
% 2.33/1.37  Inference rules
% 2.33/1.37  ----------------------
% 2.33/1.37  #Ref     : 0
% 2.33/1.37  #Sup     : 110
% 2.33/1.37  #Fact    : 0
% 2.33/1.37  #Define  : 0
% 2.33/1.37  #Split   : 4
% 2.33/1.37  #Chain   : 0
% 2.33/1.37  #Close   : 0
% 2.33/1.37  
% 2.33/1.37  Ordering : KBO
% 2.33/1.37  
% 2.33/1.37  Simplification rules
% 2.33/1.37  ----------------------
% 2.33/1.37  #Subsume      : 5
% 2.33/1.37  #Demod        : 56
% 2.33/1.37  #Tautology    : 53
% 2.33/1.37  #SimpNegUnit  : 1
% 2.33/1.37  #BackRed      : 0
% 2.33/1.37  
% 2.33/1.37  #Partial instantiations: 0
% 2.33/1.37  #Strategies tried      : 1
% 2.33/1.37  
% 2.33/1.37  Timing (in seconds)
% 2.33/1.37  ----------------------
% 2.33/1.37  Preprocessing        : 0.30
% 2.33/1.37  Parsing              : 0.17
% 2.33/1.37  CNF conversion       : 0.02
% 2.33/1.37  Main loop            : 0.25
% 2.33/1.37  Inferencing          : 0.09
% 2.33/1.37  Reduction            : 0.08
% 2.33/1.37  Demodulation         : 0.06
% 2.33/1.37  BG Simplification    : 0.02
% 2.33/1.37  Subsumption          : 0.05
% 2.33/1.37  Abstraction          : 0.02
% 2.33/1.37  MUC search           : 0.00
% 2.33/1.37  Cooper               : 0.00
% 2.33/1.37  Total                : 0.59
% 2.33/1.37  Index Insertion      : 0.00
% 2.33/1.37  Index Deletion       : 0.00
% 2.33/1.37  Index Matching       : 0.00
% 2.33/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
