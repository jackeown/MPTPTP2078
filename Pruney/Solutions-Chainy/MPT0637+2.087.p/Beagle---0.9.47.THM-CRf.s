%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 131 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 179 expanded)
%              Number of equality atoms :   43 (  86 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_54,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_12,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_307,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,k3_xboole_0(k1_relat_1(B_67),A_68)) = k7_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_337,plain,(
    ! [A_20,A_68] :
      ( k7_relat_1(k6_relat_1(A_20),k3_xboole_0(A_20,A_68)) = k7_relat_1(k6_relat_1(A_20),A_68)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_307])).

tff(c_347,plain,(
    ! [A_20,A_68] : k7_relat_1(k6_relat_1(A_20),k3_xboole_0(A_20,A_68)) = k7_relat_1(k6_relat_1(A_20),A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_337])).

tff(c_22,plain,(
    ! [A_21] : k4_relat_1(k6_relat_1(A_21)) = k6_relat_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [B_49,A_50] :
      ( k7_relat_1(B_49,A_50) = B_49
      | ~ r1_tarski(k1_relat_1(B_49),A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_153,plain,(
    ! [A_20,A_50] :
      ( k7_relat_1(k6_relat_1(A_20),A_50) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_50)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_144])).

tff(c_166,plain,(
    ! [A_55,A_56] :
      ( k7_relat_1(k6_relat_1(A_55),A_56) = k6_relat_1(A_55)
      | ~ r1_tarski(A_55,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_101,plain,(
    ! [B_43,A_44] :
      ( k3_xboole_0(k1_relat_1(B_43),A_44) = k1_relat_1(k7_relat_1(B_43,A_44))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_43,A_44)),k1_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2])).

tff(c_172,plain,(
    ! [A_55,A_56] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_55)),k1_relat_1(k6_relat_1(A_55)))
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ r1_tarski(A_55,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_107])).

tff(c_187,plain,(
    ! [A_57,A_58] :
      ( r1_tarski(A_57,A_57)
      | ~ r1_tarski(A_57,A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_18,c_172])).

tff(c_193,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_187])).

tff(c_113,plain,(
    ! [A_20,A_44] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_20),A_44)) = k3_xboole_0(A_20,A_44)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_117,plain,(
    ! [A_20,A_44] : k1_relat_1(k7_relat_1(k6_relat_1(A_20),A_44)) = k3_xboole_0(A_20,A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_175,plain,(
    ! [A_55,A_56] :
      ( k3_xboole_0(A_55,A_56) = k1_relat_1(k6_relat_1(A_55))
      | ~ r1_tarski(A_55,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_117])).

tff(c_194,plain,(
    ! [A_59,A_60] :
      ( k3_xboole_0(A_59,A_60) = A_59
      | ~ r1_tarski(A_59,A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_202,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_194])).

tff(c_156,plain,(
    ! [A_20,A_50] :
      ( k7_relat_1(k6_relat_1(A_20),A_50) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_328,plain,(
    ! [A_20,A_68] :
      ( k7_relat_1(k6_relat_1(A_20),A_68) = k6_relat_1(A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ r1_tarski(A_20,k3_xboole_0(k1_relat_1(k6_relat_1(A_20)),A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_307])).

tff(c_472,plain,(
    ! [A_75,A_76] :
      ( k7_relat_1(k6_relat_1(A_75),A_76) = k6_relat_1(A_75)
      | ~ r1_tarski(A_75,k3_xboole_0(A_75,A_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12,c_328])).

tff(c_481,plain,(
    ! [A_1,B_2] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1) = k6_relat_1(k3_xboole_0(A_1,B_2))
      | ~ r1_tarski(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_472])).

tff(c_489,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),A_1) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_481])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_453,plain,(
    ! [B_73,A_74] :
      ( k5_relat_1(k4_relat_1(B_73),k4_relat_1(A_74)) = k4_relat_1(k5_relat_1(A_74,B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_462,plain,(
    ! [A_21,A_74] :
      ( k5_relat_1(k6_relat_1(A_21),k4_relat_1(A_74)) = k4_relat_1(k5_relat_1(A_74,k6_relat_1(A_21)))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_453])).

tff(c_536,plain,(
    ! [A_79,A_80] :
      ( k5_relat_1(k6_relat_1(A_79),k4_relat_1(A_80)) = k4_relat_1(k5_relat_1(A_80,k6_relat_1(A_79)))
      | ~ v1_relat_1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_462])).

tff(c_552,plain,(
    ! [A_21,A_79] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_79))) = k5_relat_1(k6_relat_1(A_79),k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_536])).

tff(c_557,plain,(
    ! [A_81,A_82] : k4_relat_1(k5_relat_1(k6_relat_1(A_81),k6_relat_1(A_82))) = k5_relat_1(k6_relat_1(A_82),k6_relat_1(A_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_552])).

tff(c_576,plain,(
    ! [A_82,A_24] :
      ( k5_relat_1(k6_relat_1(A_82),k6_relat_1(A_24)) = k4_relat_1(k7_relat_1(k6_relat_1(A_82),A_24))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_557])).

tff(c_583,plain,(
    ! [A_83,A_84] : k5_relat_1(k6_relat_1(A_83),k6_relat_1(A_84)) = k4_relat_1(k7_relat_1(k6_relat_1(A_83),A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_576])).

tff(c_589,plain,(
    ! [A_83,A_84] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_83),A_84)) = k7_relat_1(k6_relat_1(A_84),A_83)
      | ~ v1_relat_1(k6_relat_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_26])).

tff(c_610,plain,(
    ! [A_85,A_86] : k4_relat_1(k7_relat_1(k6_relat_1(A_85),A_86)) = k7_relat_1(k6_relat_1(A_86),A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_589])).

tff(c_628,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2)) = k4_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_610])).

tff(c_641,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),B_2) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_22,c_628])).

tff(c_30,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_89,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_91,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.36  
% 2.31/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.36  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.31/1.36  
% 2.31/1.36  %Foreground sorts:
% 2.31/1.36  
% 2.31/1.36  
% 2.31/1.36  %Background operators:
% 2.31/1.36  
% 2.31/1.36  
% 2.31/1.36  %Foreground operators:
% 2.31/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.31/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.31/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.36  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.31/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.36  
% 2.31/1.37  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.31/1.37  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.31/1.37  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.31/1.37  tff(f_54, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 2.31/1.37  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.31/1.37  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.31/1.37  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.31/1.37  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.31/1.37  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.31/1.37  tff(f_71, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.31/1.37  tff(c_12, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.37  tff(c_18, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.37  tff(c_307, plain, (![B_67, A_68]: (k7_relat_1(B_67, k3_xboole_0(k1_relat_1(B_67), A_68))=k7_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.37  tff(c_337, plain, (![A_20, A_68]: (k7_relat_1(k6_relat_1(A_20), k3_xboole_0(A_20, A_68))=k7_relat_1(k6_relat_1(A_20), A_68) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_307])).
% 2.31/1.37  tff(c_347, plain, (![A_20, A_68]: (k7_relat_1(k6_relat_1(A_20), k3_xboole_0(A_20, A_68))=k7_relat_1(k6_relat_1(A_20), A_68))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_337])).
% 2.31/1.37  tff(c_22, plain, (![A_21]: (k4_relat_1(k6_relat_1(A_21))=k6_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.31/1.37  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.37  tff(c_144, plain, (![B_49, A_50]: (k7_relat_1(B_49, A_50)=B_49 | ~r1_tarski(k1_relat_1(B_49), A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.31/1.37  tff(c_153, plain, (![A_20, A_50]: (k7_relat_1(k6_relat_1(A_20), A_50)=k6_relat_1(A_20) | ~r1_tarski(A_20, A_50) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_144])).
% 2.31/1.37  tff(c_166, plain, (![A_55, A_56]: (k7_relat_1(k6_relat_1(A_55), A_56)=k6_relat_1(A_55) | ~r1_tarski(A_55, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_153])).
% 2.31/1.37  tff(c_101, plain, (![B_43, A_44]: (k3_xboole_0(k1_relat_1(B_43), A_44)=k1_relat_1(k7_relat_1(B_43, A_44)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.31/1.37  tff(c_107, plain, (![B_43, A_44]: (r1_tarski(k1_relat_1(k7_relat_1(B_43, A_44)), k1_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2])).
% 2.31/1.37  tff(c_172, plain, (![A_55, A_56]: (r1_tarski(k1_relat_1(k6_relat_1(A_55)), k1_relat_1(k6_relat_1(A_55))) | ~v1_relat_1(k6_relat_1(A_55)) | ~r1_tarski(A_55, A_56))), inference(superposition, [status(thm), theory('equality')], [c_166, c_107])).
% 2.31/1.37  tff(c_187, plain, (![A_57, A_58]: (r1_tarski(A_57, A_57) | ~r1_tarski(A_57, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_18, c_172])).
% 2.31/1.37  tff(c_193, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_187])).
% 2.31/1.37  tff(c_113, plain, (![A_20, A_44]: (k1_relat_1(k7_relat_1(k6_relat_1(A_20), A_44))=k3_xboole_0(A_20, A_44) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_101])).
% 2.31/1.37  tff(c_117, plain, (![A_20, A_44]: (k1_relat_1(k7_relat_1(k6_relat_1(A_20), A_44))=k3_xboole_0(A_20, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_113])).
% 2.31/1.37  tff(c_175, plain, (![A_55, A_56]: (k3_xboole_0(A_55, A_56)=k1_relat_1(k6_relat_1(A_55)) | ~r1_tarski(A_55, A_56))), inference(superposition, [status(thm), theory('equality')], [c_166, c_117])).
% 2.31/1.37  tff(c_194, plain, (![A_59, A_60]: (k3_xboole_0(A_59, A_60)=A_59 | ~r1_tarski(A_59, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_175])).
% 2.31/1.37  tff(c_202, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_194])).
% 2.31/1.37  tff(c_156, plain, (![A_20, A_50]: (k7_relat_1(k6_relat_1(A_20), A_50)=k6_relat_1(A_20) | ~r1_tarski(A_20, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_153])).
% 2.31/1.37  tff(c_328, plain, (![A_20, A_68]: (k7_relat_1(k6_relat_1(A_20), A_68)=k6_relat_1(A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~r1_tarski(A_20, k3_xboole_0(k1_relat_1(k6_relat_1(A_20)), A_68)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_307])).
% 2.31/1.37  tff(c_472, plain, (![A_75, A_76]: (k7_relat_1(k6_relat_1(A_75), A_76)=k6_relat_1(A_75) | ~r1_tarski(A_75, k3_xboole_0(A_75, A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12, c_328])).
% 2.31/1.37  tff(c_481, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1)=k6_relat_1(k3_xboole_0(A_1, B_2)) | ~r1_tarski(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_472])).
% 2.31/1.37  tff(c_489, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), A_1)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_481])).
% 2.31/1.37  tff(c_26, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.37  tff(c_453, plain, (![B_73, A_74]: (k5_relat_1(k4_relat_1(B_73), k4_relat_1(A_74))=k4_relat_1(k5_relat_1(A_74, B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.37  tff(c_462, plain, (![A_21, A_74]: (k5_relat_1(k6_relat_1(A_21), k4_relat_1(A_74))=k4_relat_1(k5_relat_1(A_74, k6_relat_1(A_21))) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_22, c_453])).
% 2.31/1.37  tff(c_536, plain, (![A_79, A_80]: (k5_relat_1(k6_relat_1(A_79), k4_relat_1(A_80))=k4_relat_1(k5_relat_1(A_80, k6_relat_1(A_79))) | ~v1_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_462])).
% 2.31/1.37  tff(c_552, plain, (![A_21, A_79]: (k4_relat_1(k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_79)))=k5_relat_1(k6_relat_1(A_79), k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_536])).
% 2.31/1.37  tff(c_557, plain, (![A_81, A_82]: (k4_relat_1(k5_relat_1(k6_relat_1(A_81), k6_relat_1(A_82)))=k5_relat_1(k6_relat_1(A_82), k6_relat_1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_552])).
% 2.31/1.37  tff(c_576, plain, (![A_82, A_24]: (k5_relat_1(k6_relat_1(A_82), k6_relat_1(A_24))=k4_relat_1(k7_relat_1(k6_relat_1(A_82), A_24)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_557])).
% 2.31/1.37  tff(c_583, plain, (![A_83, A_84]: (k5_relat_1(k6_relat_1(A_83), k6_relat_1(A_84))=k4_relat_1(k7_relat_1(k6_relat_1(A_83), A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_576])).
% 2.31/1.37  tff(c_589, plain, (![A_83, A_84]: (k4_relat_1(k7_relat_1(k6_relat_1(A_83), A_84))=k7_relat_1(k6_relat_1(A_84), A_83) | ~v1_relat_1(k6_relat_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_583, c_26])).
% 2.31/1.37  tff(c_610, plain, (![A_85, A_86]: (k4_relat_1(k7_relat_1(k6_relat_1(A_85), A_86))=k7_relat_1(k6_relat_1(A_86), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_589])).
% 2.31/1.37  tff(c_628, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2))=k4_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_489, c_610])).
% 2.31/1.37  tff(c_641, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), B_2)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_22, c_628])).
% 2.31/1.37  tff(c_30, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.31/1.37  tff(c_89, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_30])).
% 2.31/1.37  tff(c_91, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 2.31/1.37  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_91])).
% 2.31/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  Inference rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Ref     : 0
% 2.31/1.37  #Sup     : 143
% 2.31/1.37  #Fact    : 0
% 2.31/1.37  #Define  : 0
% 2.31/1.37  #Split   : 2
% 2.31/1.37  #Chain   : 0
% 2.31/1.37  #Close   : 0
% 2.31/1.38  
% 2.31/1.38  Ordering : KBO
% 2.31/1.38  
% 2.31/1.38  Simplification rules
% 2.31/1.38  ----------------------
% 2.31/1.38  #Subsume      : 6
% 2.31/1.38  #Demod        : 119
% 2.31/1.38  #Tautology    : 83
% 2.31/1.38  #SimpNegUnit  : 0
% 2.31/1.38  #BackRed      : 10
% 2.31/1.38  
% 2.31/1.38  #Partial instantiations: 0
% 2.31/1.38  #Strategies tried      : 1
% 2.31/1.38  
% 2.31/1.38  Timing (in seconds)
% 2.31/1.38  ----------------------
% 2.31/1.38  Preprocessing        : 0.29
% 2.31/1.38  Parsing              : 0.16
% 2.31/1.38  CNF conversion       : 0.02
% 2.31/1.38  Main loop            : 0.27
% 2.31/1.38  Inferencing          : 0.11
% 2.31/1.38  Reduction            : 0.09
% 2.31/1.38  Demodulation         : 0.07
% 2.31/1.38  BG Simplification    : 0.02
% 2.31/1.38  Subsumption          : 0.04
% 2.31/1.38  Abstraction          : 0.02
% 2.31/1.38  MUC search           : 0.00
% 2.31/1.38  Cooper               : 0.00
% 2.31/1.38  Total                : 0.60
% 2.31/1.38  Index Insertion      : 0.00
% 2.31/1.38  Index Deletion       : 0.00
% 2.31/1.38  Index Matching       : 0.00
% 2.31/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
