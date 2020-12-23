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
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.51s
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

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

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

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_137,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k5_relat_1(A_31,B_32)) = k1_relat_1(A_31)
      | ~ r1_tarski(k2_relat_1(A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_146,plain,(
    ! [B_32] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_32)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_137])).

tff(c_153,plain,(
    ! [B_33] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_33)) = k1_xboole_0
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12,c_28,c_146])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_162,plain,(
    ! [B_33] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_33))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_18])).

tff(c_170,plain,(
    ! [B_34] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_162])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_188,plain,(
    ! [B_36] :
      ( k5_relat_1(k1_xboole_0,B_36) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_192,plain,(
    ! [B_7] :
      ( k5_relat_1(k1_xboole_0,B_7) = k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_188])).

tff(c_235,plain,(
    ! [B_38] :
      ( k5_relat_1(k1_xboole_0,B_38) = k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_192])).

tff(c_244,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_235])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_244])).

tff(c_251,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_298,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_46,B_47)),k2_relat_1(B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_306,plain,(
    ! [A_46] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_46,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_298])).

tff(c_312,plain,(
    ! [A_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_306])).

tff(c_269,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_278,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_269])).

tff(c_322,plain,(
    ! [A_49] :
      ( k2_relat_1(k5_relat_1(A_49,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_312,c_278])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_337,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_49,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_49,k1_xboole_0))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_20])).

tff(c_400,plain,(
    ! [A_54] :
      ( ~ v1_relat_1(k5_relat_1(A_54,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_54,k1_xboole_0))
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_337])).

tff(c_491,plain,(
    ! [A_58] :
      ( k5_relat_1(A_58,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_58,k1_xboole_0))
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_400,c_4])).

tff(c_498,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_491])).

tff(c_551,plain,(
    ! [A_61] :
      ( k5_relat_1(A_61,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_498])).

tff(c_560,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_551])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:51:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.36  
% 2.33/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.36  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.33/1.36  
% 2.33/1.36  %Foreground sorts:
% 2.33/1.36  
% 2.33/1.36  
% 2.33/1.36  %Background operators:
% 2.33/1.36  
% 2.33/1.36  
% 2.33/1.36  %Foreground operators:
% 2.33/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.36  
% 2.51/1.37  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.51/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.51/1.37  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.51/1.37  tff(f_48, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.51/1.37  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.37  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.51/1.37  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.51/1.37  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.51/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.51/1.37  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.51/1.37  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.37  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.51/1.37  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.37  tff(c_55, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.51/1.37  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.51/1.37  tff(c_50, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.51/1.37  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.51/1.37  tff(c_16, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.37  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.37  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.37  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.37  tff(c_137, plain, (![A_31, B_32]: (k1_relat_1(k5_relat_1(A_31, B_32))=k1_relat_1(A_31) | ~r1_tarski(k2_relat_1(A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.51/1.37  tff(c_146, plain, (![B_32]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_32))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_137])).
% 2.51/1.37  tff(c_153, plain, (![B_33]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_33))=k1_xboole_0 | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12, c_28, c_146])).
% 2.51/1.37  tff(c_18, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.37  tff(c_162, plain, (![B_33]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_33)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_33)) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_153, c_18])).
% 2.51/1.37  tff(c_170, plain, (![B_34]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_162])).
% 2.51/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.51/1.37  tff(c_188, plain, (![B_36]: (k5_relat_1(k1_xboole_0, B_36)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_170, c_4])).
% 2.51/1.37  tff(c_192, plain, (![B_7]: (k5_relat_1(k1_xboole_0, B_7)=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_188])).
% 2.51/1.37  tff(c_235, plain, (![B_38]: (k5_relat_1(k1_xboole_0, B_38)=k1_xboole_0 | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_192])).
% 2.51/1.37  tff(c_244, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_235])).
% 2.51/1.37  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_244])).
% 2.51/1.37  tff(c_251, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.51/1.37  tff(c_298, plain, (![A_46, B_47]: (r1_tarski(k2_relat_1(k5_relat_1(A_46, B_47)), k2_relat_1(B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.37  tff(c_306, plain, (![A_46]: (r1_tarski(k2_relat_1(k5_relat_1(A_46, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_26, c_298])).
% 2.51/1.37  tff(c_312, plain, (![A_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_48, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_306])).
% 2.51/1.37  tff(c_269, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.51/1.37  tff(c_278, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_269])).
% 2.51/1.37  tff(c_322, plain, (![A_49]: (k2_relat_1(k5_relat_1(A_49, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_312, c_278])).
% 2.51/1.37  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.37  tff(c_337, plain, (![A_49]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_49, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_49, k1_xboole_0)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_322, c_20])).
% 2.51/1.37  tff(c_400, plain, (![A_54]: (~v1_relat_1(k5_relat_1(A_54, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_54, k1_xboole_0)) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_337])).
% 2.51/1.37  tff(c_491, plain, (![A_58]: (k5_relat_1(A_58, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_58, k1_xboole_0)) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_400, c_4])).
% 2.51/1.37  tff(c_498, plain, (![A_6]: (k5_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_491])).
% 2.51/1.37  tff(c_551, plain, (![A_61]: (k5_relat_1(A_61, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_498])).
% 2.51/1.37  tff(c_560, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_551])).
% 2.51/1.37  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_560])).
% 2.51/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  Inference rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Ref     : 0
% 2.51/1.37  #Sup     : 111
% 2.51/1.37  #Fact    : 0
% 2.51/1.37  #Define  : 0
% 2.51/1.37  #Split   : 1
% 2.51/1.37  #Chain   : 0
% 2.51/1.37  #Close   : 0
% 2.51/1.37  
% 2.51/1.37  Ordering : KBO
% 2.51/1.37  
% 2.51/1.37  Simplification rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Subsume      : 5
% 2.51/1.37  #Demod        : 115
% 2.51/1.37  #Tautology    : 66
% 2.51/1.37  #SimpNegUnit  : 2
% 2.51/1.37  #BackRed      : 0
% 2.51/1.37  
% 2.51/1.37  #Partial instantiations: 0
% 2.51/1.37  #Strategies tried      : 1
% 2.51/1.37  
% 2.51/1.37  Timing (in seconds)
% 2.51/1.37  ----------------------
% 2.51/1.38  Preprocessing        : 0.29
% 2.51/1.38  Parsing              : 0.17
% 2.51/1.38  CNF conversion       : 0.02
% 2.51/1.38  Main loop            : 0.26
% 2.51/1.38  Inferencing          : 0.10
% 2.51/1.38  Reduction            : 0.07
% 2.51/1.38  Demodulation         : 0.05
% 2.51/1.38  BG Simplification    : 0.01
% 2.51/1.38  Subsumption          : 0.05
% 2.51/1.38  Abstraction          : 0.01
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.58
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
