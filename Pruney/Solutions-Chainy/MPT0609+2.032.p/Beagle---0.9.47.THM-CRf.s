%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 11.17s
% Output     : CNFRefutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 158 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :   93 ( 244 expanded)
%              Number of equality atoms :   37 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k6_subset_1(B_21,k7_relat_1(B_21,A_20))) = k6_subset_1(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k4_xboole_0(B_21,k7_relat_1(B_21,A_20))) = k4_xboole_0(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_18])).

tff(c_14,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_17,B_19] :
      ( k7_relat_1(A_17,k1_relat_1(k7_relat_1(B_19,k1_relat_1(A_17)))) = k7_relat_1(A_17,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    ! [B_47,A_48] :
      ( k1_relat_1(k7_relat_1(B_47,A_48)) = A_48
      | ~ r1_tarski(A_48,k1_relat_1(B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1393,plain,(
    ! [B_109,B_110] :
      ( k1_relat_1(k7_relat_1(B_109,k1_relat_1(k7_relat_1(B_110,k1_relat_1(B_109))))) = k1_relat_1(k7_relat_1(B_110,k1_relat_1(B_109)))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_13559,plain,(
    ! [B_213,A_214] :
      ( k1_relat_1(k7_relat_1(B_213,k1_relat_1(A_214))) = k1_relat_1(k7_relat_1(A_214,k1_relat_1(B_213)))
      | ~ v1_relat_1(A_214)
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1393])).

tff(c_192,plain,(
    ! [A_61,B_62] :
      ( k7_relat_1(A_61,k1_relat_1(k7_relat_1(B_62,k1_relat_1(A_61)))) = k7_relat_1(A_61,k1_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_241,plain,(
    ! [A_22,B_62] :
      ( k7_relat_1(k6_relat_1(A_22),k1_relat_1(k7_relat_1(B_62,A_22))) = k7_relat_1(k6_relat_1(A_22),k1_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_192])).

tff(c_253,plain,(
    ! [A_22,B_62] :
      ( k7_relat_1(k6_relat_1(A_22),k1_relat_1(k7_relat_1(B_62,A_22))) = k7_relat_1(k6_relat_1(A_22),k1_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_241])).

tff(c_1570,plain,(
    ! [A_22,B_110] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_22),k1_relat_1(k7_relat_1(B_110,A_22)))) = k1_relat_1(k7_relat_1(B_110,k1_relat_1(k6_relat_1(A_22))))
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1393])).

tff(c_1611,plain,(
    ! [A_111,B_112] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_111),k1_relat_1(k7_relat_1(B_112,A_111)))) = k1_relat_1(k7_relat_1(B_112,A_111))
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_1570])).

tff(c_2488,plain,(
    ! [A_122,B_123] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_122),k1_relat_1(B_123))) = k1_relat_1(k7_relat_1(B_123,A_122))
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_1611])).

tff(c_2705,plain,(
    ! [A_22,A_122] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_22),A_122)) = k1_relat_1(k7_relat_1(k6_relat_1(A_122),A_22))
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2488])).

tff(c_2747,plain,(
    ! [A_22,A_122] : k1_relat_1(k7_relat_1(k6_relat_1(A_22),A_122)) = k1_relat_1(k7_relat_1(k6_relat_1(A_122),A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_2705])).

tff(c_2748,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(k1_relat_1(A_124),k1_relat_1(k7_relat_1(B_125,k1_relat_1(A_124)))) = k1_relat_1(k4_xboole_0(A_124,k7_relat_1(A_124,k1_relat_1(B_125))))
      | ~ v1_relat_1(A_124)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_31])).

tff(c_2863,plain,(
    ! [A_22,B_125] :
      ( k1_relat_1(k4_xboole_0(k6_relat_1(A_22),k7_relat_1(k6_relat_1(A_22),k1_relat_1(B_125)))) = k4_xboole_0(A_22,k1_relat_1(k7_relat_1(B_125,k1_relat_1(k6_relat_1(A_22)))))
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2748])).

tff(c_9992,plain,(
    ! [A_182,B_183] :
      ( k1_relat_1(k4_xboole_0(k6_relat_1(A_182),k7_relat_1(k6_relat_1(A_182),k1_relat_1(B_183)))) = k4_xboole_0(A_182,k1_relat_1(k7_relat_1(B_183,A_182)))
      | ~ v1_relat_1(B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20,c_2863])).

tff(c_10072,plain,(
    ! [A_182,B_183] :
      ( k4_xboole_0(k1_relat_1(k6_relat_1(A_182)),k1_relat_1(B_183)) = k4_xboole_0(A_182,k1_relat_1(k7_relat_1(B_183,A_182)))
      | ~ v1_relat_1(k6_relat_1(A_182))
      | ~ v1_relat_1(B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9992,c_31])).

tff(c_10201,plain,(
    ! [A_184,B_185] :
      ( k4_xboole_0(A_184,k1_relat_1(k7_relat_1(B_185,A_184))) = k4_xboole_0(A_184,k1_relat_1(B_185))
      | ~ v1_relat_1(B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_10072])).

tff(c_10266,plain,(
    ! [A_22,A_122] :
      ( k4_xboole_0(A_22,k1_relat_1(k7_relat_1(k6_relat_1(A_22),A_122))) = k4_xboole_0(A_22,k1_relat_1(k6_relat_1(A_122)))
      | ~ v1_relat_1(k6_relat_1(A_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2747,c_10201])).

tff(c_10404,plain,(
    ! [A_188,A_189] : k4_xboole_0(A_188,k1_relat_1(k7_relat_1(k6_relat_1(A_188),A_189))) = k4_xboole_0(A_188,A_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_10266])).

tff(c_10466,plain,(
    ! [A_122,A_22] : k4_xboole_0(A_122,k1_relat_1(k7_relat_1(k6_relat_1(A_22),A_122))) = k4_xboole_0(A_122,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_2747,c_10404])).

tff(c_13673,plain,(
    ! [A_214,A_22] :
      ( k4_xboole_0(k1_relat_1(A_214),k1_relat_1(k7_relat_1(A_214,k1_relat_1(k6_relat_1(A_22))))) = k4_xboole_0(k1_relat_1(A_214),A_22)
      | ~ v1_relat_1(A_214)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13559,c_10466])).

tff(c_16357,plain,(
    ! [A_225,A_226] :
      ( k4_xboole_0(k1_relat_1(A_225),k1_relat_1(k7_relat_1(A_225,A_226))) = k4_xboole_0(k1_relat_1(A_225),A_226)
      | ~ v1_relat_1(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20,c_13673])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_28])).

tff(c_16382,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16357,c_32])).

tff(c_16598,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16382])).

tff(c_16655,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_16598])).

tff(c_16659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.17/3.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/3.64  
% 11.17/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/3.64  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 11.17/3.64  
% 11.17/3.64  %Foreground sorts:
% 11.17/3.64  
% 11.17/3.64  
% 11.17/3.64  %Background operators:
% 11.17/3.64  
% 11.17/3.64  
% 11.17/3.64  %Foreground operators:
% 11.17/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.17/3.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.17/3.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.17/3.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.17/3.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.17/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.17/3.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.17/3.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.17/3.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.17/3.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.17/3.64  tff('#skF_2', type, '#skF_2': $i).
% 11.17/3.64  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.17/3.64  tff('#skF_1', type, '#skF_1': $i).
% 11.17/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.17/3.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.17/3.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.17/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.17/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.17/3.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.17/3.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.17/3.64  
% 11.17/3.66  tff(f_69, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 11.17/3.66  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.17/3.66  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 11.17/3.66  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 11.17/3.66  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.17/3.66  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 11.17/3.66  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 11.17/3.66  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 11.17/3.66  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.17/3.66  tff(c_10, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.17/3.66  tff(c_18, plain, (![B_21, A_20]: (k1_relat_1(k6_subset_1(B_21, k7_relat_1(B_21, A_20)))=k6_subset_1(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.17/3.66  tff(c_31, plain, (![B_21, A_20]: (k1_relat_1(k4_xboole_0(B_21, k7_relat_1(B_21, A_20)))=k4_xboole_0(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_18])).
% 11.17/3.66  tff(c_14, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.17/3.66  tff(c_20, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.17/3.66  tff(c_16, plain, (![A_17, B_19]: (k7_relat_1(A_17, k1_relat_1(k7_relat_1(B_19, k1_relat_1(A_17))))=k7_relat_1(A_17, k1_relat_1(B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.17/3.66  tff(c_24, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.17/3.66  tff(c_107, plain, (![B_47, A_48]: (k1_relat_1(k7_relat_1(B_47, A_48))=A_48 | ~r1_tarski(A_48, k1_relat_1(B_47)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.17/3.66  tff(c_1393, plain, (![B_109, B_110]: (k1_relat_1(k7_relat_1(B_109, k1_relat_1(k7_relat_1(B_110, k1_relat_1(B_109)))))=k1_relat_1(k7_relat_1(B_110, k1_relat_1(B_109))) | ~v1_relat_1(B_109) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_24, c_107])).
% 11.17/3.66  tff(c_13559, plain, (![B_213, A_214]: (k1_relat_1(k7_relat_1(B_213, k1_relat_1(A_214)))=k1_relat_1(k7_relat_1(A_214, k1_relat_1(B_213))) | ~v1_relat_1(A_214) | ~v1_relat_1(B_213) | ~v1_relat_1(B_213) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1393])).
% 11.17/3.66  tff(c_192, plain, (![A_61, B_62]: (k7_relat_1(A_61, k1_relat_1(k7_relat_1(B_62, k1_relat_1(A_61))))=k7_relat_1(A_61, k1_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.17/3.66  tff(c_241, plain, (![A_22, B_62]: (k7_relat_1(k6_relat_1(A_22), k1_relat_1(k7_relat_1(B_62, A_22)))=k7_relat_1(k6_relat_1(A_22), k1_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_192])).
% 11.17/3.66  tff(c_253, plain, (![A_22, B_62]: (k7_relat_1(k6_relat_1(A_22), k1_relat_1(k7_relat_1(B_62, A_22)))=k7_relat_1(k6_relat_1(A_22), k1_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_241])).
% 11.17/3.66  tff(c_1570, plain, (![A_22, B_110]: (k1_relat_1(k7_relat_1(k6_relat_1(A_22), k1_relat_1(k7_relat_1(B_110, A_22))))=k1_relat_1(k7_relat_1(B_110, k1_relat_1(k6_relat_1(A_22)))) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1393])).
% 11.17/3.66  tff(c_1611, plain, (![A_111, B_112]: (k1_relat_1(k7_relat_1(k6_relat_1(A_111), k1_relat_1(k7_relat_1(B_112, A_111))))=k1_relat_1(k7_relat_1(B_112, A_111)) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_1570])).
% 11.17/3.66  tff(c_2488, plain, (![A_122, B_123]: (k1_relat_1(k7_relat_1(k6_relat_1(A_122), k1_relat_1(B_123)))=k1_relat_1(k7_relat_1(B_123, A_122)) | ~v1_relat_1(B_123) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_253, c_1611])).
% 11.17/3.66  tff(c_2705, plain, (![A_22, A_122]: (k1_relat_1(k7_relat_1(k6_relat_1(A_22), A_122))=k1_relat_1(k7_relat_1(k6_relat_1(A_122), A_22)) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2488])).
% 11.17/3.66  tff(c_2747, plain, (![A_22, A_122]: (k1_relat_1(k7_relat_1(k6_relat_1(A_22), A_122))=k1_relat_1(k7_relat_1(k6_relat_1(A_122), A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_2705])).
% 11.17/3.66  tff(c_2748, plain, (![A_124, B_125]: (k4_xboole_0(k1_relat_1(A_124), k1_relat_1(k7_relat_1(B_125, k1_relat_1(A_124))))=k1_relat_1(k4_xboole_0(A_124, k7_relat_1(A_124, k1_relat_1(B_125)))) | ~v1_relat_1(A_124) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_192, c_31])).
% 11.17/3.66  tff(c_2863, plain, (![A_22, B_125]: (k1_relat_1(k4_xboole_0(k6_relat_1(A_22), k7_relat_1(k6_relat_1(A_22), k1_relat_1(B_125))))=k4_xboole_0(A_22, k1_relat_1(k7_relat_1(B_125, k1_relat_1(k6_relat_1(A_22))))) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(B_125) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2748])).
% 11.17/3.66  tff(c_9992, plain, (![A_182, B_183]: (k1_relat_1(k4_xboole_0(k6_relat_1(A_182), k7_relat_1(k6_relat_1(A_182), k1_relat_1(B_183))))=k4_xboole_0(A_182, k1_relat_1(k7_relat_1(B_183, A_182))) | ~v1_relat_1(B_183))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20, c_2863])).
% 11.17/3.66  tff(c_10072, plain, (![A_182, B_183]: (k4_xboole_0(k1_relat_1(k6_relat_1(A_182)), k1_relat_1(B_183))=k4_xboole_0(A_182, k1_relat_1(k7_relat_1(B_183, A_182))) | ~v1_relat_1(k6_relat_1(A_182)) | ~v1_relat_1(B_183))), inference(superposition, [status(thm), theory('equality')], [c_9992, c_31])).
% 11.17/3.66  tff(c_10201, plain, (![A_184, B_185]: (k4_xboole_0(A_184, k1_relat_1(k7_relat_1(B_185, A_184)))=k4_xboole_0(A_184, k1_relat_1(B_185)) | ~v1_relat_1(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_10072])).
% 11.17/3.66  tff(c_10266, plain, (![A_22, A_122]: (k4_xboole_0(A_22, k1_relat_1(k7_relat_1(k6_relat_1(A_22), A_122)))=k4_xboole_0(A_22, k1_relat_1(k6_relat_1(A_122))) | ~v1_relat_1(k6_relat_1(A_122)))), inference(superposition, [status(thm), theory('equality')], [c_2747, c_10201])).
% 11.17/3.66  tff(c_10404, plain, (![A_188, A_189]: (k4_xboole_0(A_188, k1_relat_1(k7_relat_1(k6_relat_1(A_188), A_189)))=k4_xboole_0(A_188, A_189))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_10266])).
% 11.17/3.66  tff(c_10466, plain, (![A_122, A_22]: (k4_xboole_0(A_122, k1_relat_1(k7_relat_1(k6_relat_1(A_22), A_122)))=k4_xboole_0(A_122, A_22))), inference(superposition, [status(thm), theory('equality')], [c_2747, c_10404])).
% 11.17/3.66  tff(c_13673, plain, (![A_214, A_22]: (k4_xboole_0(k1_relat_1(A_214), k1_relat_1(k7_relat_1(A_214, k1_relat_1(k6_relat_1(A_22)))))=k4_xboole_0(k1_relat_1(A_214), A_22) | ~v1_relat_1(A_214) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_13559, c_10466])).
% 11.17/3.66  tff(c_16357, plain, (![A_225, A_226]: (k4_xboole_0(k1_relat_1(A_225), k1_relat_1(k7_relat_1(A_225, A_226)))=k4_xboole_0(k1_relat_1(A_225), A_226) | ~v1_relat_1(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20, c_13673])).
% 11.17/3.66  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.17/3.66  tff(c_32, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_28])).
% 11.17/3.66  tff(c_16382, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16357, c_32])).
% 11.17/3.66  tff(c_16598, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16382])).
% 11.17/3.66  tff(c_16655, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31, c_16598])).
% 11.17/3.66  tff(c_16659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_16655])).
% 11.17/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/3.66  
% 11.17/3.66  Inference rules
% 11.17/3.66  ----------------------
% 11.17/3.66  #Ref     : 0
% 11.17/3.66  #Sup     : 4145
% 11.17/3.66  #Fact    : 0
% 11.17/3.66  #Define  : 0
% 11.17/3.66  #Split   : 0
% 11.17/3.66  #Chain   : 0
% 11.17/3.66  #Close   : 0
% 11.17/3.66  
% 11.17/3.66  Ordering : KBO
% 11.17/3.66  
% 11.17/3.66  Simplification rules
% 11.17/3.66  ----------------------
% 11.17/3.66  #Subsume      : 793
% 11.17/3.66  #Demod        : 3382
% 11.17/3.66  #Tautology    : 621
% 11.17/3.66  #SimpNegUnit  : 0
% 11.17/3.66  #BackRed      : 0
% 11.17/3.66  
% 11.17/3.66  #Partial instantiations: 0
% 11.17/3.66  #Strategies tried      : 1
% 11.17/3.66  
% 11.17/3.66  Timing (in seconds)
% 11.17/3.66  ----------------------
% 11.17/3.66  Preprocessing        : 0.30
% 11.17/3.66  Parsing              : 0.16
% 11.17/3.66  CNF conversion       : 0.02
% 11.17/3.66  Main loop            : 2.61
% 11.17/3.66  Inferencing          : 0.72
% 11.17/3.66  Reduction            : 0.93
% 11.17/3.66  Demodulation         : 0.75
% 11.17/3.66  BG Simplification    : 0.14
% 11.17/3.66  Subsumption          : 0.67
% 11.17/3.66  Abstraction          : 0.18
% 11.17/3.66  MUC search           : 0.00
% 11.17/3.66  Cooper               : 0.00
% 11.17/3.66  Total                : 2.93
% 11.17/3.66  Index Insertion      : 0.00
% 11.17/3.66  Index Deletion       : 0.00
% 11.17/3.66  Index Matching       : 0.00
% 11.17/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
