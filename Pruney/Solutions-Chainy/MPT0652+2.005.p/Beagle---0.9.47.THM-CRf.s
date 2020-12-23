%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 121 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 292 expanded)
%              Number of equality atoms :   33 ( 103 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [A_18] :
      ( k4_relat_1(A_18) = k2_funct_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_61,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_58])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8])).

tff(c_80,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_72])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_76,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_10,plain,(
    ! [A_4] :
      ( k2_relat_1(k4_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_10])).

tff(c_78,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_69])).

tff(c_162,plain,(
    ! [A_23,B_24] :
      ( k1_relat_1(k5_relat_1(A_23,B_24)) = k1_relat_1(A_23)
      | ~ r1_tarski(k2_relat_1(A_23),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_174,plain,(
    ! [B_24] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_24)) = k1_relat_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_162])).

tff(c_281,plain,(
    ! [B_29] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_29)) = k2_relat_1('#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_174])).

tff(c_294,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_281])).

tff(c_301,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_301])).

tff(c_304,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_315,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8])).

tff(c_323,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_312,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_10])).

tff(c_321,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_312])).

tff(c_406,plain,(
    ! [B_34,A_35] :
      ( k2_relat_1(k5_relat_1(B_34,A_35)) = k2_relat_1(A_35)
      | ~ r1_tarski(k1_relat_1(A_35),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_418,plain,(
    ! [A_35] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_35)) = k2_relat_1(A_35)
      | ~ r1_tarski(k1_relat_1(A_35),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_406])).

tff(c_474,plain,(
    ! [A_39] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_39)) = k2_relat_1(A_39)
      | ~ r1_tarski(k1_relat_1(A_39),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_418])).

tff(c_493,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_474])).

tff(c_500,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_493])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.58/1.39  
% 2.58/1.39  %Foreground sorts:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Background operators:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Foreground operators:
% 2.58/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.39  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.58/1.39  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.39  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.58/1.39  
% 2.58/1.40  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.58/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.40  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.58/1.40  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.58/1.40  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.58/1.40  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.58/1.40  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.58/1.40  tff(c_20, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.40  tff(c_62, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.58/1.40  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.40  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.40  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.40  tff(c_55, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.40  tff(c_58, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_55])).
% 2.58/1.40  tff(c_61, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_58])).
% 2.58/1.40  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.40  tff(c_72, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_8])).
% 2.58/1.40  tff(c_80, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_72])).
% 2.58/1.40  tff(c_12, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.40  tff(c_66, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 2.58/1.40  tff(c_76, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 2.58/1.40  tff(c_10, plain, (![A_4]: (k2_relat_1(k4_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.40  tff(c_69, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_10])).
% 2.58/1.40  tff(c_78, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_69])).
% 2.58/1.40  tff(c_162, plain, (![A_23, B_24]: (k1_relat_1(k5_relat_1(A_23, B_24))=k1_relat_1(A_23) | ~r1_tarski(k2_relat_1(A_23), k1_relat_1(B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.40  tff(c_174, plain, (![B_24]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_24))=k1_relat_1(k2_funct_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_162])).
% 2.58/1.40  tff(c_281, plain, (![B_29]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_29))=k2_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_174])).
% 2.58/1.40  tff(c_294, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_281])).
% 2.58/1.40  tff(c_301, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_294])).
% 2.58/1.40  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_301])).
% 2.58/1.40  tff(c_304, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.58/1.40  tff(c_315, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_8])).
% 2.58/1.40  tff(c_323, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_315])).
% 2.58/1.40  tff(c_312, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_10])).
% 2.58/1.40  tff(c_321, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_312])).
% 2.58/1.40  tff(c_406, plain, (![B_34, A_35]: (k2_relat_1(k5_relat_1(B_34, A_35))=k2_relat_1(A_35) | ~r1_tarski(k1_relat_1(A_35), k2_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.40  tff(c_418, plain, (![A_35]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_35))=k2_relat_1(A_35) | ~r1_tarski(k1_relat_1(A_35), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_321, c_406])).
% 2.58/1.40  tff(c_474, plain, (![A_39]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_39))=k2_relat_1(A_39) | ~r1_tarski(k1_relat_1(A_39), k1_relat_1('#skF_1')) | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_418])).
% 2.58/1.40  tff(c_493, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_474])).
% 2.58/1.40  tff(c_500, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_493])).
% 2.58/1.40  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_500])).
% 2.58/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.40  
% 2.58/1.40  Inference rules
% 2.58/1.40  ----------------------
% 2.58/1.40  #Ref     : 0
% 2.58/1.40  #Sup     : 117
% 2.58/1.40  #Fact    : 0
% 2.58/1.40  #Define  : 0
% 2.58/1.40  #Split   : 5
% 2.58/1.40  #Chain   : 0
% 2.58/1.40  #Close   : 0
% 2.58/1.40  
% 2.58/1.40  Ordering : KBO
% 2.58/1.40  
% 2.58/1.40  Simplification rules
% 2.58/1.40  ----------------------
% 2.58/1.40  #Subsume      : 5
% 2.58/1.40  #Demod        : 64
% 2.58/1.40  #Tautology    : 35
% 2.58/1.40  #SimpNegUnit  : 2
% 2.58/1.40  #BackRed      : 0
% 2.58/1.40  
% 2.58/1.40  #Partial instantiations: 0
% 2.58/1.40  #Strategies tried      : 1
% 2.58/1.40  
% 2.58/1.40  Timing (in seconds)
% 2.58/1.40  ----------------------
% 2.58/1.40  Preprocessing        : 0.32
% 2.58/1.40  Parsing              : 0.17
% 2.58/1.40  CNF conversion       : 0.02
% 2.58/1.40  Main loop            : 0.29
% 2.58/1.40  Inferencing          : 0.10
% 2.58/1.40  Reduction            : 0.09
% 2.58/1.40  Demodulation         : 0.06
% 2.58/1.40  BG Simplification    : 0.02
% 2.58/1.40  Subsumption          : 0.07
% 2.58/1.40  Abstraction          : 0.02
% 2.58/1.40  MUC search           : 0.00
% 2.58/1.40  Cooper               : 0.00
% 2.58/1.40  Total                : 0.64
% 2.58/1.40  Index Insertion      : 0.00
% 2.58/1.41  Index Deletion       : 0.00
% 2.58/1.41  Index Matching       : 0.00
% 2.58/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
