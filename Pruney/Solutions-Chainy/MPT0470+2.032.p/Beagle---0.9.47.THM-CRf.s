%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   60 (  93 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 166 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_27,B_28)),k1_relat_1(A_27))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [B_28] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_28)),k1_xboole_0)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_101,plain,(
    ! [B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_29)),k1_xboole_0)
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_97])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [B_22,A_23] :
      ( B_22 = A_23
      | ~ r1_tarski(B_22,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_111,plain,(
    ! [B_30] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_30)) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_101,c_77])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [B_30] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_30))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_18])).

tff(c_179,plain,(
    ! [B_35] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_315,plain,(
    ! [B_39] :
      ( k5_relat_1(k1_xboole_0,B_39) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_179,c_4])).

tff(c_322,plain,(
    ! [B_7] :
      ( k5_relat_1(k1_xboole_0,B_7) = k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_315])).

tff(c_328,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_322])).

tff(c_337,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_328])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_337])).

tff(c_345,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_466,plain,(
    ! [B_53,A_54] :
      ( k2_relat_1(k5_relat_1(B_53,A_54)) = k2_relat_1(A_54)
      | ~ r1_tarski(k1_relat_1(A_54),k2_relat_1(B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_472,plain,(
    ! [B_53] :
      ( k2_relat_1(k5_relat_1(B_53,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_466])).

tff(c_482,plain,(
    ! [B_55] :
      ( k2_relat_1(k5_relat_1(B_55,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12,c_26,c_472])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_491,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_55,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_55,k1_xboole_0))
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_20])).

tff(c_499,plain,(
    ! [B_56] :
      ( ~ v1_relat_1(k5_relat_1(B_56,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_56,k1_xboole_0))
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_491])).

tff(c_508,plain,(
    ! [B_57] :
      ( k5_relat_1(B_57,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_57,k1_xboole_0))
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_499,c_4])).

tff(c_512,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_508])).

tff(c_529,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_512])).

tff(c_538,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_529])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.30  
% 2.40/1.31  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.40/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.40/1.31  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.40/1.31  tff(f_48, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.40/1.31  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.40/1.31  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.40/1.31  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.40/1.31  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.31  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.40/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.40/1.31  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.40/1.31  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.40/1.31  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.40/1.31  tff(c_55, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.40/1.31  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.40/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.40/1.31  tff(c_50, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.31  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.40/1.31  tff(c_16, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.31  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.40/1.31  tff(c_92, plain, (![A_27, B_28]: (r1_tarski(k1_relat_1(k5_relat_1(A_27, B_28)), k1_relat_1(A_27)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.40/1.31  tff(c_97, plain, (![B_28]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_28)), k1_xboole_0) | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_92])).
% 2.40/1.31  tff(c_101, plain, (![B_29]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_29)), k1_xboole_0) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_97])).
% 2.40/1.31  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.31  tff(c_68, plain, (![B_22, A_23]: (B_22=A_23 | ~r1_tarski(B_22, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.40/1.31  tff(c_77, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_68])).
% 2.40/1.31  tff(c_111, plain, (![B_30]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_30))=k1_xboole_0 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_101, c_77])).
% 2.40/1.31  tff(c_18, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.31  tff(c_126, plain, (![B_30]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_30)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_30)) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_111, c_18])).
% 2.40/1.31  tff(c_179, plain, (![B_35]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_126])).
% 2.40/1.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.40/1.31  tff(c_315, plain, (![B_39]: (k5_relat_1(k1_xboole_0, B_39)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_179, c_4])).
% 2.40/1.31  tff(c_322, plain, (![B_7]: (k5_relat_1(k1_xboole_0, B_7)=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_315])).
% 2.40/1.31  tff(c_328, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_322])).
% 2.40/1.31  tff(c_337, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_328])).
% 2.40/1.31  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_337])).
% 2.40/1.31  tff(c_345, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.40/1.31  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.40/1.31  tff(c_466, plain, (![B_53, A_54]: (k2_relat_1(k5_relat_1(B_53, A_54))=k2_relat_1(A_54) | ~r1_tarski(k1_relat_1(A_54), k2_relat_1(B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.31  tff(c_472, plain, (![B_53]: (k2_relat_1(k5_relat_1(B_53, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_466])).
% 2.40/1.31  tff(c_482, plain, (![B_55]: (k2_relat_1(k5_relat_1(B_55, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12, c_26, c_472])).
% 2.40/1.31  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.31  tff(c_491, plain, (![B_55]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_55, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_55, k1_xboole_0)) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_482, c_20])).
% 2.40/1.31  tff(c_499, plain, (![B_56]: (~v1_relat_1(k5_relat_1(B_56, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_56, k1_xboole_0)) | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_491])).
% 2.40/1.31  tff(c_508, plain, (![B_57]: (k5_relat_1(B_57, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_57, k1_xboole_0)) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_499, c_4])).
% 2.40/1.31  tff(c_512, plain, (![A_6]: (k5_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_508])).
% 2.40/1.31  tff(c_529, plain, (![A_59]: (k5_relat_1(A_59, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_512])).
% 2.40/1.31  tff(c_538, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_529])).
% 2.40/1.31  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_538])).
% 2.40/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  Inference rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Ref     : 0
% 2.40/1.31  #Sup     : 106
% 2.40/1.31  #Fact    : 0
% 2.40/1.31  #Define  : 0
% 2.40/1.31  #Split   : 1
% 2.40/1.31  #Chain   : 0
% 2.40/1.31  #Close   : 0
% 2.40/1.31  
% 2.40/1.31  Ordering : KBO
% 2.40/1.31  
% 2.40/1.31  Simplification rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Subsume      : 5
% 2.40/1.31  #Demod        : 115
% 2.40/1.31  #Tautology    : 63
% 2.40/1.31  #SimpNegUnit  : 2
% 2.40/1.31  #BackRed      : 1
% 2.40/1.31  
% 2.40/1.31  #Partial instantiations: 0
% 2.40/1.31  #Strategies tried      : 1
% 2.40/1.31  
% 2.40/1.31  Timing (in seconds)
% 2.40/1.31  ----------------------
% 2.40/1.32  Preprocessing        : 0.28
% 2.40/1.32  Parsing              : 0.16
% 2.40/1.32  CNF conversion       : 0.02
% 2.40/1.32  Main loop            : 0.26
% 2.40/1.32  Inferencing          : 0.10
% 2.40/1.32  Reduction            : 0.07
% 2.40/1.32  Demodulation         : 0.05
% 2.40/1.32  BG Simplification    : 0.01
% 2.40/1.32  Subsumption          : 0.05
% 2.40/1.32  Abstraction          : 0.01
% 2.40/1.32  MUC search           : 0.00
% 2.40/1.32  Cooper               : 0.00
% 2.40/1.32  Total                : 0.58
% 2.40/1.32  Index Insertion      : 0.00
% 2.40/1.32  Index Deletion       : 0.00
% 2.40/1.32  Index Matching       : 0.00
% 2.40/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
