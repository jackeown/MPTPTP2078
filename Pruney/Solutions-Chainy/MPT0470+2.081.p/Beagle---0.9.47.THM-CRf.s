%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 162 expanded)
%              Number of equality atoms :   28 (  46 expanded)
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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_24,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_53,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_15] :
      ( v1_relat_1(A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,(
    ! [A_24,B_25] :
      ( k1_relat_1(k5_relat_1(A_24,B_25)) = k1_relat_1(A_24)
      | ~ r1_tarski(k2_relat_1(A_24),k1_relat_1(B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    ! [B_25] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_25)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_89])).

tff(c_105,plain,(
    ! [B_26] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_26)) = k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_22,c_98])).

tff(c_12,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [B_26] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_26))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_12])).

tff(c_136,plain,(
    ! [B_28] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_28))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_214,plain,(
    ! [B_31] :
      ( k5_relat_1(k1_xboole_0,B_31) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_221,plain,(
    ! [B_5] :
      ( k5_relat_1(k1_xboole_0,B_5) = k1_xboole_0
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_214])).

tff(c_227,plain,(
    ! [B_32] :
      ( k5_relat_1(k1_xboole_0,B_32) = k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_221])).

tff(c_236,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_227])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_236])).

tff(c_244,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_355,plain,(
    ! [B_42,A_43] :
      ( k2_relat_1(k5_relat_1(B_42,A_43)) = k2_relat_1(A_43)
      | ~ r1_tarski(k1_relat_1(A_43),k2_relat_1(B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_361,plain,(
    ! [B_42] :
      ( k2_relat_1(k5_relat_1(B_42,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_355])).

tff(c_371,plain,(
    ! [B_44] :
      ( k2_relat_1(k5_relat_1(B_44,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_20,c_361])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_383,plain,(
    ! [B_44] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_44,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_44,k1_xboole_0))
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_14])).

tff(c_398,plain,(
    ! [B_45] :
      ( ~ v1_relat_1(k5_relat_1(B_45,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_45,k1_xboole_0))
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_383])).

tff(c_412,plain,(
    ! [B_46] :
      ( k5_relat_1(B_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_46,k1_xboole_0))
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_398,c_4])).

tff(c_419,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_412])).

tff(c_467,plain,(
    ! [A_49] :
      ( k5_relat_1(A_49,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_419])).

tff(c_476,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_467])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.28  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.17/1.28  
% 2.17/1.28  %Foreground sorts:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Background operators:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Foreground operators:
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.28  
% 2.17/1.30  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.17/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.30  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.17/1.30  tff(f_42, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.17/1.30  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.17/1.30  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.17/1.30  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.17/1.30  tff(f_50, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.17/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.17/1.30  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.17/1.30  tff(f_58, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.17/1.30  tff(c_24, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.30  tff(c_53, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 2.17/1.30  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.30  tff(c_36, plain, (![A_15]: (v1_relat_1(A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.30  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 2.17/1.30  tff(c_10, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.30  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.30  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.30  tff(c_89, plain, (![A_24, B_25]: (k1_relat_1(k5_relat_1(A_24, B_25))=k1_relat_1(A_24) | ~r1_tarski(k2_relat_1(A_24), k1_relat_1(B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.30  tff(c_98, plain, (![B_25]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_25))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_89])).
% 2.17/1.30  tff(c_105, plain, (![B_26]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_26))=k1_xboole_0 | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_22, c_98])).
% 2.17/1.30  tff(c_12, plain, (![A_6]: (~v1_xboole_0(k1_relat_1(A_6)) | ~v1_relat_1(A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.30  tff(c_117, plain, (![B_26]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_26)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_26)) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_105, c_12])).
% 2.17/1.30  tff(c_136, plain, (![B_28]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_28)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_28)) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_117])).
% 2.17/1.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.17/1.30  tff(c_214, plain, (![B_31]: (k5_relat_1(k1_xboole_0, B_31)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_31)) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_136, c_4])).
% 2.17/1.30  tff(c_221, plain, (![B_5]: (k5_relat_1(k1_xboole_0, B_5)=k1_xboole_0 | ~v1_relat_1(B_5) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_214])).
% 2.17/1.30  tff(c_227, plain, (![B_32]: (k5_relat_1(k1_xboole_0, B_32)=k1_xboole_0 | ~v1_relat_1(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_221])).
% 2.17/1.30  tff(c_236, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_227])).
% 2.17/1.30  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_236])).
% 2.17/1.30  tff(c_244, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.17/1.30  tff(c_355, plain, (![B_42, A_43]: (k2_relat_1(k5_relat_1(B_42, A_43))=k2_relat_1(A_43) | ~r1_tarski(k1_relat_1(A_43), k2_relat_1(B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.30  tff(c_361, plain, (![B_42]: (k2_relat_1(k5_relat_1(B_42, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_355])).
% 2.17/1.30  tff(c_371, plain, (![B_44]: (k2_relat_1(k5_relat_1(B_44, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_20, c_361])).
% 2.17/1.30  tff(c_14, plain, (![A_7]: (~v1_xboole_0(k2_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.30  tff(c_383, plain, (![B_44]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_44, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_44, k1_xboole_0)) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_371, c_14])).
% 2.17/1.30  tff(c_398, plain, (![B_45]: (~v1_relat_1(k5_relat_1(B_45, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_45, k1_xboole_0)) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_383])).
% 2.17/1.30  tff(c_412, plain, (![B_46]: (k5_relat_1(B_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_46, k1_xboole_0)) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_398, c_4])).
% 2.17/1.30  tff(c_419, plain, (![A_4]: (k5_relat_1(A_4, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_10, c_412])).
% 2.17/1.30  tff(c_467, plain, (![A_49]: (k5_relat_1(A_49, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_419])).
% 2.17/1.30  tff(c_476, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_467])).
% 2.17/1.30  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_476])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 97
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 1
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 4
% 2.17/1.30  #Demod        : 111
% 2.17/1.30  #Tautology    : 59
% 2.17/1.30  #SimpNegUnit  : 2
% 2.17/1.30  #BackRed      : 0
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.30  Preprocessing        : 0.28
% 2.17/1.30  Parsing              : 0.16
% 2.17/1.30  CNF conversion       : 0.02
% 2.17/1.30  Main loop            : 0.23
% 2.17/1.30  Inferencing          : 0.09
% 2.17/1.30  Reduction            : 0.07
% 2.17/1.30  Demodulation         : 0.05
% 2.17/1.30  BG Simplification    : 0.01
% 2.17/1.30  Subsumption          : 0.04
% 2.17/1.30  Abstraction          : 0.01
% 2.17/1.30  MUC search           : 0.00
% 2.17/1.30  Cooper               : 0.00
% 2.17/1.30  Total                : 0.54
% 2.17/1.30  Index Insertion      : 0.00
% 2.17/1.30  Index Deletion       : 0.00
% 2.17/1.30  Index Matching       : 0.00
% 2.17/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
