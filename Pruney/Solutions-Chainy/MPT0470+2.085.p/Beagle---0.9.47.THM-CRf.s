%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 178 expanded)
%              Number of equality atoms :   29 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_26,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_59,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    ! [A_17] :
      ( v1_relat_1(A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_28,B_29)),k1_relat_1(A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    ! [B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_29)),k1_xboole_0)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_84,plain,(
    ! [B_30] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_30)),k1_xboole_0)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_80])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_87,plain,(
    ! [B_30] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_30)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_90,plain,(
    ! [B_31] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_31)) = k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [B_31] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_31))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_14])).

tff(c_138,plain,(
    ! [B_34] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_49,plain,(
    ! [B_19,A_20] :
      ( ~ v1_xboole_0(B_19)
      | B_19 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_150,plain,(
    ! [B_35] :
      ( k5_relat_1(k1_xboole_0,B_35) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_138,c_52])).

tff(c_154,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_168,plain,(
    ! [B_38] :
      ( k5_relat_1(k1_xboole_0,B_38) = k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_154])).

tff(c_177,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_177])).

tff(c_184,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_209,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_45,B_46)),k2_relat_1(B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_218,plain,(
    ! [A_45] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_45,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_209])).

tff(c_322,plain,(
    ! [A_53] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_53,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_218])).

tff(c_325,plain,(
    ! [A_53] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_53,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_53,k1_xboole_0))
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_322,c_4])).

tff(c_328,plain,(
    ! [A_54] :
      ( k2_relat_1(k5_relat_1(A_54,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_325])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_343,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_54,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_54,k1_xboole_0))
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_16])).

tff(c_399,plain,(
    ! [A_58] :
      ( ~ v1_relat_1(k5_relat_1(A_58,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_58,k1_xboole_0))
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_343])).

tff(c_564,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_63,k1_xboole_0))
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_399,c_52])).

tff(c_571,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_564])).

tff(c_577,plain,(
    ! [A_64] :
      ( k5_relat_1(A_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_571])).

tff(c_586,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_577])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.41/1.33  
% 2.41/1.33  %Foreground sorts:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Background operators:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Foreground operators:
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.41/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.41/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.33  
% 2.41/1.34  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.41/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.41/1.34  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.41/1.34  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.41/1.34  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.41/1.34  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.41/1.34  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.41/1.34  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.41/1.34  tff(f_58, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.41/1.34  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.41/1.34  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.41/1.34  tff(f_66, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.41/1.34  tff(c_26, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.34  tff(c_59, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 2.41/1.34  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.41/1.34  tff(c_37, plain, (![A_17]: (v1_relat_1(A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.34  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_37])).
% 2.41/1.34  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.34  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.41/1.34  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.34  tff(c_74, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k5_relat_1(A_28, B_29)), k1_relat_1(A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.41/1.34  tff(c_80, plain, (![B_29]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_29)), k1_xboole_0) | ~v1_relat_1(B_29) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_74])).
% 2.41/1.34  tff(c_84, plain, (![B_30]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_30)), k1_xboole_0) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_80])).
% 2.41/1.34  tff(c_4, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.41/1.34  tff(c_87, plain, (![B_30]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_30)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_30)) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_84, c_4])).
% 2.41/1.34  tff(c_90, plain, (![B_31]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_31))=k1_xboole_0 | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_87])).
% 2.41/1.34  tff(c_14, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.34  tff(c_105, plain, (![B_31]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_31)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_31)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_90, c_14])).
% 2.41/1.34  tff(c_138, plain, (![B_34]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_105])).
% 2.41/1.34  tff(c_49, plain, (![B_19, A_20]: (~v1_xboole_0(B_19) | B_19=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.34  tff(c_52, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.41/1.34  tff(c_150, plain, (![B_35]: (k5_relat_1(k1_xboole_0, B_35)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_138, c_52])).
% 2.41/1.34  tff(c_154, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_150])).
% 2.41/1.34  tff(c_168, plain, (![B_38]: (k5_relat_1(k1_xboole_0, B_38)=k1_xboole_0 | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_154])).
% 2.41/1.34  tff(c_177, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_168])).
% 2.41/1.34  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_177])).
% 2.41/1.34  tff(c_184, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.41/1.34  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.34  tff(c_209, plain, (![A_45, B_46]: (r1_tarski(k2_relat_1(k5_relat_1(A_45, B_46)), k2_relat_1(B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.41/1.34  tff(c_218, plain, (![A_45]: (r1_tarski(k2_relat_1(k5_relat_1(A_45, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_22, c_209])).
% 2.41/1.34  tff(c_322, plain, (![A_53]: (r1_tarski(k2_relat_1(k5_relat_1(A_53, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_218])).
% 2.41/1.34  tff(c_325, plain, (![A_53]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_53, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_53, k1_xboole_0)) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_322, c_4])).
% 2.41/1.34  tff(c_328, plain, (![A_54]: (k2_relat_1(k5_relat_1(A_54, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_325])).
% 2.41/1.34  tff(c_16, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.34  tff(c_343, plain, (![A_54]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_54, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_54, k1_xboole_0)) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_328, c_16])).
% 2.41/1.34  tff(c_399, plain, (![A_58]: (~v1_relat_1(k5_relat_1(A_58, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_58, k1_xboole_0)) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_343])).
% 2.41/1.34  tff(c_564, plain, (![A_63]: (k5_relat_1(A_63, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_63, k1_xboole_0)) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_399, c_52])).
% 2.41/1.34  tff(c_571, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_564])).
% 2.41/1.34  tff(c_577, plain, (![A_64]: (k5_relat_1(A_64, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_571])).
% 2.41/1.34  tff(c_586, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_577])).
% 2.41/1.34  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_586])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 119
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 2
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Subsume      : 15
% 2.41/1.34  #Demod        : 162
% 2.41/1.34  #Tautology    : 67
% 2.41/1.34  #SimpNegUnit  : 6
% 2.41/1.34  #BackRed      : 3
% 2.41/1.34  
% 2.41/1.34  #Partial instantiations: 0
% 2.41/1.34  #Strategies tried      : 1
% 2.41/1.34  
% 2.41/1.34  Timing (in seconds)
% 2.41/1.34  ----------------------
% 2.41/1.35  Preprocessing        : 0.27
% 2.41/1.35  Parsing              : 0.16
% 2.41/1.35  CNF conversion       : 0.02
% 2.41/1.35  Main loop            : 0.27
% 2.41/1.35  Inferencing          : 0.11
% 2.41/1.35  Reduction            : 0.08
% 2.41/1.35  Demodulation         : 0.06
% 2.41/1.35  BG Simplification    : 0.01
% 2.41/1.35  Subsumption          : 0.05
% 2.41/1.35  Abstraction          : 0.01
% 2.41/1.35  MUC search           : 0.00
% 2.41/1.35  Cooper               : 0.00
% 2.41/1.35  Total                : 0.58
% 2.41/1.35  Index Insertion      : 0.00
% 2.41/1.35  Index Deletion       : 0.00
% 2.41/1.35  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
