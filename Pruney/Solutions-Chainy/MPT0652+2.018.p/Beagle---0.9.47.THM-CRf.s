%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 130 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 360 expanded)
%              Number of equality atoms :   30 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [B_22,A_23] :
      ( k7_relat_1(B_22,A_23) = B_22
      | ~ r1_tarski(k1_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_416,plain,(
    ! [B_54] :
      ( k7_relat_1(B_54,k1_relat_1(B_54)) = B_54
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_422,plain,(
    ! [B_54] :
      ( k9_relat_1(B_54,k1_relat_1(B_54)) = k2_relat_1(B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_8])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_471,plain,(
    ! [B_58,A_59] :
      ( k9_relat_1(B_58,k2_relat_1(A_59)) = k2_relat_1(k5_relat_1(A_59,B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_556,plain,(
    ! [A_68,B_69] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_68),B_69)) = k9_relat_1(B_69,k1_relat_1(A_68))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(k2_funct_1(A_68))
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_471])).

tff(c_22,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,(
    ! [A_30,B_31] :
      ( k1_relat_1(k5_relat_1(A_30,B_31)) = k1_relat_1(A_30)
      | ~ r1_tarski(k2_relat_1(A_30),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_332,plain,(
    ! [A_51,B_52] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_51),B_52)) = k1_relat_1(k2_funct_1(A_51))
      | ~ r1_tarski(k1_relat_1(A_51),k1_relat_1(B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(k2_funct_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_121])).

tff(c_350,plain,(
    ! [A_53] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_53),A_53)) = k1_relat_1(k2_funct_1(A_53))
      | ~ v1_relat_1(k2_funct_1(A_53))
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_332])).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_57,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_379,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_57])).

tff(c_388,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_379])).

tff(c_390,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_393,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_390])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_393])).

tff(c_398,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_402,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_398])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_402])).

tff(c_407,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_574,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_407])).

tff(c_580,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_30,c_574])).

tff(c_582,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_585,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_582])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_585])).

tff(c_590,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_594,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_590])).

tff(c_598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.69/1.40  
% 2.69/1.40  %Foreground sorts:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Background operators:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Foreground operators:
% 2.69/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.69/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.69/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.69/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.40  
% 2.69/1.41  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.69/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.41  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.69/1.41  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.69/1.41  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.69/1.41  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.69/1.41  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.69/1.41  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.69/1.41  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.41  tff(c_51, plain, (![B_22, A_23]: (k7_relat_1(B_22, A_23)=B_22 | ~r1_tarski(k1_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.41  tff(c_416, plain, (![B_54]: (k7_relat_1(B_54, k1_relat_1(B_54))=B_54 | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_6, c_51])).
% 2.69/1.41  tff(c_8, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_422, plain, (![B_54]: (k9_relat_1(B_54, k1_relat_1(B_54))=k2_relat_1(B_54) | ~v1_relat_1(B_54) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_416, c_8])).
% 2.69/1.41  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.41  tff(c_18, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.41  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.41  tff(c_20, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.41  tff(c_471, plain, (![B_58, A_59]: (k9_relat_1(B_58, k2_relat_1(A_59))=k2_relat_1(k5_relat_1(A_59, B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.41  tff(c_556, plain, (![A_68, B_69]: (k2_relat_1(k5_relat_1(k2_funct_1(A_68), B_69))=k9_relat_1(B_69, k1_relat_1(A_68)) | ~v1_relat_1(B_69) | ~v1_relat_1(k2_funct_1(A_68)) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_20, c_471])).
% 2.69/1.41  tff(c_22, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.41  tff(c_121, plain, (![A_30, B_31]: (k1_relat_1(k5_relat_1(A_30, B_31))=k1_relat_1(A_30) | ~r1_tarski(k2_relat_1(A_30), k1_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.41  tff(c_332, plain, (![A_51, B_52]: (k1_relat_1(k5_relat_1(k2_funct_1(A_51), B_52))=k1_relat_1(k2_funct_1(A_51)) | ~r1_tarski(k1_relat_1(A_51), k1_relat_1(B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(k2_funct_1(A_51)) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_20, c_121])).
% 2.69/1.41  tff(c_350, plain, (![A_53]: (k1_relat_1(k5_relat_1(k2_funct_1(A_53), A_53))=k1_relat_1(k2_funct_1(A_53)) | ~v1_relat_1(k2_funct_1(A_53)) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_6, c_332])).
% 2.69/1.41  tff(c_24, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.41  tff(c_57, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.69/1.41  tff(c_379, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_350, c_57])).
% 2.69/1.41  tff(c_388, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_379])).
% 2.69/1.41  tff(c_390, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_388])).
% 2.69/1.41  tff(c_393, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_390])).
% 2.69/1.41  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_393])).
% 2.69/1.41  tff(c_398, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_388])).
% 2.69/1.41  tff(c_402, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_398])).
% 2.69/1.41  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_402])).
% 2.69/1.41  tff(c_407, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.69/1.41  tff(c_574, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_556, c_407])).
% 2.69/1.41  tff(c_580, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_30, c_574])).
% 2.69/1.41  tff(c_582, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_580])).
% 2.69/1.41  tff(c_585, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_582])).
% 2.69/1.41  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_585])).
% 2.69/1.41  tff(c_590, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_580])).
% 2.69/1.41  tff(c_594, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_422, c_590])).
% 2.69/1.41  tff(c_598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_594])).
% 2.69/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  Inference rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Ref     : 0
% 2.69/1.41  #Sup     : 151
% 2.69/1.41  #Fact    : 0
% 2.69/1.41  #Define  : 0
% 2.69/1.41  #Split   : 4
% 2.69/1.41  #Chain   : 0
% 2.69/1.41  #Close   : 0
% 2.69/1.41  
% 2.69/1.41  Ordering : KBO
% 2.69/1.41  
% 2.69/1.41  Simplification rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Subsume      : 7
% 2.69/1.41  #Demod        : 17
% 2.69/1.41  #Tautology    : 46
% 2.69/1.41  #SimpNegUnit  : 0
% 2.69/1.41  #BackRed      : 0
% 2.69/1.41  
% 2.69/1.41  #Partial instantiations: 0
% 2.69/1.41  #Strategies tried      : 1
% 2.69/1.41  
% 2.69/1.41  Timing (in seconds)
% 2.69/1.41  ----------------------
% 2.69/1.42  Preprocessing        : 0.30
% 2.69/1.42  Parsing              : 0.16
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.34
% 2.69/1.42  Inferencing          : 0.13
% 2.69/1.42  Reduction            : 0.09
% 2.69/1.42  Demodulation         : 0.06
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.07
% 2.69/1.42  Abstraction          : 0.02
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.67
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
