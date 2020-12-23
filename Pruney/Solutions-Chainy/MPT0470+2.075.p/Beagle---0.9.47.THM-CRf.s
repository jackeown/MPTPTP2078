%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 164 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_56,axiom,(
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

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,(
    ! [A_33,B_34] :
      ( k1_relat_1(k5_relat_1(A_33,B_34)) = k1_relat_1(A_33)
      | ~ r1_tarski(k2_relat_1(A_33),k1_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_128,plain,(
    ! [B_34] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_34)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_119])).

tff(c_134,plain,(
    ! [B_35] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_35)) = k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10,c_28,c_128])).

tff(c_18,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_143,plain,(
    ! [B_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_18])).

tff(c_182,plain,(
    ! [B_37] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_37))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_200,plain,(
    ! [B_39] :
      ( k5_relat_1(k1_xboole_0,B_39) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_182,c_4])).

tff(c_204,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_200])).

tff(c_231,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_204])).

tff(c_240,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_240])).

tff(c_247,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_12,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_298,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_52,B_53)),k2_relat_1(B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_307,plain,(
    ! [A_52] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_52,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_298])).

tff(c_313,plain,(
    ! [A_54] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_54,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_307])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k1_xboole_0
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_316,plain,(
    ! [A_54] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_54,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_313,c_8])).

tff(c_319,plain,(
    ! [A_55] :
      ( k2_relat_1(k5_relat_1(A_55,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_316])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_334,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_55,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_55,k1_xboole_0))
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_20])).

tff(c_345,plain,(
    ! [A_56] :
      ( ~ v1_relat_1(k5_relat_1(A_56,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_56,k1_xboole_0))
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_334])).

tff(c_509,plain,(
    ! [A_65] :
      ( k5_relat_1(A_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_65,k1_xboole_0))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_345,c_4])).

tff(c_516,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_509])).

tff(c_522,plain,(
    ! [A_66] :
      ( k5_relat_1(A_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_516])).

tff(c_531,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_522])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.39  
% 2.23/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.39  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.23/1.39  
% 2.23/1.39  %Foreground sorts:
% 2.23/1.39  
% 2.23/1.39  
% 2.23/1.39  %Background operators:
% 2.23/1.39  
% 2.23/1.39  
% 2.23/1.39  %Foreground operators:
% 2.23/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.39  
% 2.48/1.40  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.48/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.40  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.48/1.40  tff(f_48, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.48/1.40  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.48/1.40  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.48/1.40  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.48/1.40  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.48/1.40  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.48/1.40  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.48/1.40  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.48/1.40  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.48/1.40  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.48/1.40  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.48/1.40  tff(c_62, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.48/1.40  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.48/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.48/1.40  tff(c_42, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.48/1.40  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_42])).
% 2.48/1.40  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.40  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.48/1.40  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.40  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.40  tff(c_119, plain, (![A_33, B_34]: (k1_relat_1(k5_relat_1(A_33, B_34))=k1_relat_1(A_33) | ~r1_tarski(k2_relat_1(A_33), k1_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.40  tff(c_128, plain, (![B_34]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_34))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_119])).
% 2.48/1.40  tff(c_134, plain, (![B_35]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_35))=k1_xboole_0 | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10, c_28, c_128])).
% 2.48/1.40  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.40  tff(c_143, plain, (![B_35]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_134, c_18])).
% 2.48/1.40  tff(c_182, plain, (![B_37]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_37)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_143])).
% 2.48/1.40  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.48/1.40  tff(c_200, plain, (![B_39]: (k5_relat_1(k1_xboole_0, B_39)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_182, c_4])).
% 2.48/1.40  tff(c_204, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_200])).
% 2.48/1.40  tff(c_231, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_204])).
% 2.48/1.40  tff(c_240, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_231])).
% 2.48/1.40  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_240])).
% 2.48/1.40  tff(c_247, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.48/1.40  tff(c_12, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.40  tff(c_298, plain, (![A_52, B_53]: (r1_tarski(k2_relat_1(k5_relat_1(A_52, B_53)), k2_relat_1(B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.40  tff(c_307, plain, (![A_52]: (r1_tarski(k2_relat_1(k5_relat_1(A_52, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_26, c_298])).
% 2.48/1.40  tff(c_313, plain, (![A_54]: (r1_tarski(k2_relat_1(k5_relat_1(A_54, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_307])).
% 2.48/1.40  tff(c_8, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k1_xboole_0 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.40  tff(c_316, plain, (![A_54]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_54, k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_313, c_8])).
% 2.48/1.40  tff(c_319, plain, (![A_55]: (k2_relat_1(k5_relat_1(A_55, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_316])).
% 2.48/1.40  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.48/1.40  tff(c_334, plain, (![A_55]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_55, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_55, k1_xboole_0)) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_319, c_20])).
% 2.48/1.40  tff(c_345, plain, (![A_56]: (~v1_relat_1(k5_relat_1(A_56, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_56, k1_xboole_0)) | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_334])).
% 2.48/1.40  tff(c_509, plain, (![A_65]: (k5_relat_1(A_65, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_65, k1_xboole_0)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_345, c_4])).
% 2.48/1.40  tff(c_516, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_16, c_509])).
% 2.48/1.40  tff(c_522, plain, (![A_66]: (k5_relat_1(A_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_516])).
% 2.48/1.40  tff(c_531, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_522])).
% 2.48/1.40  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_531])).
% 2.48/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.40  
% 2.48/1.40  Inference rules
% 2.48/1.40  ----------------------
% 2.48/1.40  #Ref     : 0
% 2.48/1.40  #Sup     : 107
% 2.48/1.40  #Fact    : 0
% 2.48/1.40  #Define  : 0
% 2.48/1.40  #Split   : 1
% 2.48/1.40  #Chain   : 0
% 2.48/1.40  #Close   : 0
% 2.48/1.40  
% 2.48/1.40  Ordering : KBO
% 2.48/1.40  
% 2.48/1.40  Simplification rules
% 2.48/1.40  ----------------------
% 2.48/1.40  #Subsume      : 5
% 2.48/1.40  #Demod        : 104
% 2.48/1.40  #Tautology    : 64
% 2.48/1.40  #SimpNegUnit  : 2
% 2.48/1.40  #BackRed      : 0
% 2.48/1.40  
% 2.48/1.40  #Partial instantiations: 0
% 2.48/1.40  #Strategies tried      : 1
% 2.48/1.40  
% 2.48/1.40  Timing (in seconds)
% 2.48/1.40  ----------------------
% 2.48/1.41  Preprocessing        : 0.31
% 2.48/1.41  Parsing              : 0.17
% 2.48/1.41  CNF conversion       : 0.02
% 2.48/1.41  Main loop            : 0.26
% 2.48/1.41  Inferencing          : 0.11
% 2.48/1.41  Reduction            : 0.07
% 2.48/1.41  Demodulation         : 0.05
% 2.48/1.41  BG Simplification    : 0.02
% 2.48/1.41  Subsumption          : 0.05
% 2.48/1.41  Abstraction          : 0.01
% 2.48/1.41  MUC search           : 0.00
% 2.48/1.41  Cooper               : 0.00
% 2.48/1.41  Total                : 0.61
% 2.48/1.41  Index Insertion      : 0.00
% 2.48/1.41  Index Deletion       : 0.00
% 2.48/1.41  Index Matching       : 0.00
% 2.48/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
