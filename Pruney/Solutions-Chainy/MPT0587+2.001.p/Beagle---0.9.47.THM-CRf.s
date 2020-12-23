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
% DateTime   : Thu Dec  3 10:02:02 EST 2020

% Result     : Theorem 14.99s
% Output     : CNFRefutation 14.99s
% Verified   : 
% Statistics : Number of formulae       :   71 (  76 expanded)
%              Number of leaves         :   39 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 (  88 expanded)
%              Number of equality atoms :   38 (  43 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_85,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_522,plain,(
    ! [C_196,D_201,E_200,G_202,F_198,B_197,A_199] : k6_enumset1(A_199,A_199,B_197,C_196,D_201,E_200,F_198,G_202) = k5_enumset1(A_199,B_197,C_196,D_201,E_200,F_198,G_202) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [J_48,C_39,B_38,A_37,D_40,G_43,E_41,H_44] : r2_hidden(J_48,k6_enumset1(A_37,B_38,C_39,D_40,E_41,J_48,G_43,H_44)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_555,plain,(
    ! [C_204,B_205,E_207,D_203,G_206,A_208,F_209] : r2_hidden(E_207,k5_enumset1(A_208,B_205,C_204,D_203,E_207,F_209,G_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_32])).

tff(c_563,plain,(
    ! [B_211,D_215,C_210,A_214,E_212,F_213] : r2_hidden(D_215,k4_enumset1(A_214,B_211,C_210,D_215,E_212,F_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_555])).

tff(c_571,plain,(
    ! [D_220,E_217,C_216,B_218,A_219] : r2_hidden(C_216,k3_enumset1(A_219,B_218,C_216,D_220,E_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_563])).

tff(c_623,plain,(
    ! [B_230,A_231,C_232,D_233] : r2_hidden(B_230,k2_enumset1(A_231,B_230,C_232,D_233)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_571])).

tff(c_631,plain,(
    ! [A_234,B_235,C_236] : r2_hidden(A_234,k1_enumset1(A_234,B_235,C_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_623])).

tff(c_639,plain,(
    ! [A_237,B_238] : r2_hidden(A_237,k2_tarski(A_237,B_238)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_631])).

tff(c_82,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_160,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k1_setfam_1(B_66),A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_163,plain,(
    ! [A_51,B_52,A_67] :
      ( r1_tarski(k3_xboole_0(A_51,B_52),A_67)
      | ~ r2_hidden(A_67,k2_tarski(A_51,B_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_160])).

tff(c_674,plain,(
    ! [A_237,B_238] : r1_tarski(k3_xboole_0(A_237,B_238),A_237) ),
    inference(resolution,[status(thm)],[c_639,c_163])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_363,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_tarski(k5_xboole_0(A_136,C_137),B_138)
      | ~ r1_tarski(C_137,B_138)
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [B_56,A_55] :
      ( k1_relat_1(k7_relat_1(B_56,A_55)) = A_55
      | ~ r1_tarski(A_55,k1_relat_1(B_56))
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1698,plain,(
    ! [B_574,A_575,C_576] :
      ( k1_relat_1(k7_relat_1(B_574,k5_xboole_0(A_575,C_576))) = k5_xboole_0(A_575,C_576)
      | ~ v1_relat_1(B_574)
      | ~ r1_tarski(C_576,k1_relat_1(B_574))
      | ~ r1_tarski(A_575,k1_relat_1(B_574)) ) ),
    inference(resolution,[status(thm)],[c_363,c_86])).

tff(c_1734,plain,(
    ! [A_3,B_4,B_574] :
      ( k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k1_relat_1(k7_relat_1(B_574,k4_xboole_0(A_3,B_4)))
      | ~ v1_relat_1(B_574)
      | ~ r1_tarski(k3_xboole_0(A_3,B_4),k1_relat_1(B_574))
      | ~ r1_tarski(A_3,k1_relat_1(B_574)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1698])).

tff(c_3949,plain,(
    ! [B_718,A_719,B_720] :
      ( k1_relat_1(k7_relat_1(B_718,k4_xboole_0(A_719,B_720))) = k4_xboole_0(A_719,B_720)
      | ~ v1_relat_1(B_718)
      | ~ r1_tarski(k3_xboole_0(A_719,B_720),k1_relat_1(B_718))
      | ~ r1_tarski(A_719,k1_relat_1(B_718)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1734])).

tff(c_3974,plain,(
    ! [B_718,B_238] :
      ( k1_relat_1(k7_relat_1(B_718,k4_xboole_0(k1_relat_1(B_718),B_238))) = k4_xboole_0(k1_relat_1(B_718),B_238)
      | ~ v1_relat_1(B_718)
      | ~ r1_tarski(k1_relat_1(B_718),k1_relat_1(B_718)) ) ),
    inference(resolution,[status(thm)],[c_674,c_3949])).

tff(c_3995,plain,(
    ! [B_721,B_722] :
      ( k1_relat_1(k7_relat_1(B_721,k4_xboole_0(k1_relat_1(B_721),B_722))) = k4_xboole_0(k1_relat_1(B_721),B_722)
      | ~ v1_relat_1(B_721) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3974])).

tff(c_80,plain,(
    ! [A_49,B_50] : k6_subset_1(A_49,B_50) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_88,plain,(
    k1_relat_1(k7_relat_1('#skF_4',k6_subset_1(k1_relat_1('#skF_4'),'#skF_3'))) != k6_subset_1(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_91,plain,(
    k1_relat_1(k7_relat_1('#skF_4',k4_xboole_0(k1_relat_1('#skF_4'),'#skF_3'))) != k4_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_88])).

tff(c_4050,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3995,c_91])).

tff(c_4093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.99/8.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.99/8.58  
% 14.99/8.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.99/8.58  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.99/8.58  
% 14.99/8.58  %Foreground sorts:
% 14.99/8.58  
% 14.99/8.58  
% 14.99/8.58  %Background operators:
% 14.99/8.58  
% 14.99/8.58  
% 14.99/8.58  %Foreground operators:
% 14.99/8.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.99/8.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.99/8.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.99/8.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.99/8.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.99/8.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.99/8.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.99/8.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.99/8.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.99/8.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.99/8.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.99/8.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 14.99/8.58  tff('#skF_3', type, '#skF_3': $i).
% 14.99/8.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.99/8.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.99/8.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.99/8.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.99/8.58  tff('#skF_4', type, '#skF_4': $i).
% 14.99/8.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.99/8.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.99/8.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.99/8.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.99/8.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.99/8.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.99/8.58  
% 14.99/8.59  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 14.99/8.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.99/8.59  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 14.99/8.59  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 14.99/8.59  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 14.99/8.59  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 14.99/8.59  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 14.99/8.59  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 14.99/8.59  tff(f_83, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 14.99/8.59  tff(f_87, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.99/8.59  tff(f_91, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 14.99/8.59  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.99/8.59  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 14.99/8.59  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 14.99/8.59  tff(f_85, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.99/8.59  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.99/8.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.99/8.59  tff(c_14, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.99/8.59  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.99/8.59  tff(c_18, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.99/8.59  tff(c_20, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.99/8.59  tff(c_22, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.99/8.59  tff(c_522, plain, (![C_196, D_201, E_200, G_202, F_198, B_197, A_199]: (k6_enumset1(A_199, A_199, B_197, C_196, D_201, E_200, F_198, G_202)=k5_enumset1(A_199, B_197, C_196, D_201, E_200, F_198, G_202))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.99/8.59  tff(c_32, plain, (![J_48, C_39, B_38, A_37, D_40, G_43, E_41, H_44]: (r2_hidden(J_48, k6_enumset1(A_37, B_38, C_39, D_40, E_41, J_48, G_43, H_44)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.99/8.59  tff(c_555, plain, (![C_204, B_205, E_207, D_203, G_206, A_208, F_209]: (r2_hidden(E_207, k5_enumset1(A_208, B_205, C_204, D_203, E_207, F_209, G_206)))), inference(superposition, [status(thm), theory('equality')], [c_522, c_32])).
% 14.99/8.59  tff(c_563, plain, (![B_211, D_215, C_210, A_214, E_212, F_213]: (r2_hidden(D_215, k4_enumset1(A_214, B_211, C_210, D_215, E_212, F_213)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_555])).
% 14.99/8.59  tff(c_571, plain, (![D_220, E_217, C_216, B_218, A_219]: (r2_hidden(C_216, k3_enumset1(A_219, B_218, C_216, D_220, E_217)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_563])).
% 14.99/8.59  tff(c_623, plain, (![B_230, A_231, C_232, D_233]: (r2_hidden(B_230, k2_enumset1(A_231, B_230, C_232, D_233)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_571])).
% 14.99/8.59  tff(c_631, plain, (![A_234, B_235, C_236]: (r2_hidden(A_234, k1_enumset1(A_234, B_235, C_236)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_623])).
% 14.99/8.59  tff(c_639, plain, (![A_237, B_238]: (r2_hidden(A_237, k2_tarski(A_237, B_238)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_631])).
% 14.99/8.59  tff(c_82, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.99/8.59  tff(c_160, plain, (![B_66, A_67]: (r1_tarski(k1_setfam_1(B_66), A_67) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.99/8.59  tff(c_163, plain, (![A_51, B_52, A_67]: (r1_tarski(k3_xboole_0(A_51, B_52), A_67) | ~r2_hidden(A_67, k2_tarski(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_160])).
% 14.99/8.59  tff(c_674, plain, (![A_237, B_238]: (r1_tarski(k3_xboole_0(A_237, B_238), A_237))), inference(resolution, [status(thm)], [c_639, c_163])).
% 14.99/8.59  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.99/8.59  tff(c_363, plain, (![A_136, C_137, B_138]: (r1_tarski(k5_xboole_0(A_136, C_137), B_138) | ~r1_tarski(C_137, B_138) | ~r1_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.99/8.59  tff(c_86, plain, (![B_56, A_55]: (k1_relat_1(k7_relat_1(B_56, A_55))=A_55 | ~r1_tarski(A_55, k1_relat_1(B_56)) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.99/8.59  tff(c_1698, plain, (![B_574, A_575, C_576]: (k1_relat_1(k7_relat_1(B_574, k5_xboole_0(A_575, C_576)))=k5_xboole_0(A_575, C_576) | ~v1_relat_1(B_574) | ~r1_tarski(C_576, k1_relat_1(B_574)) | ~r1_tarski(A_575, k1_relat_1(B_574)))), inference(resolution, [status(thm)], [c_363, c_86])).
% 14.99/8.59  tff(c_1734, plain, (![A_3, B_4, B_574]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k1_relat_1(k7_relat_1(B_574, k4_xboole_0(A_3, B_4))) | ~v1_relat_1(B_574) | ~r1_tarski(k3_xboole_0(A_3, B_4), k1_relat_1(B_574)) | ~r1_tarski(A_3, k1_relat_1(B_574)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1698])).
% 14.99/8.59  tff(c_3949, plain, (![B_718, A_719, B_720]: (k1_relat_1(k7_relat_1(B_718, k4_xboole_0(A_719, B_720)))=k4_xboole_0(A_719, B_720) | ~v1_relat_1(B_718) | ~r1_tarski(k3_xboole_0(A_719, B_720), k1_relat_1(B_718)) | ~r1_tarski(A_719, k1_relat_1(B_718)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1734])).
% 14.99/8.59  tff(c_3974, plain, (![B_718, B_238]: (k1_relat_1(k7_relat_1(B_718, k4_xboole_0(k1_relat_1(B_718), B_238)))=k4_xboole_0(k1_relat_1(B_718), B_238) | ~v1_relat_1(B_718) | ~r1_tarski(k1_relat_1(B_718), k1_relat_1(B_718)))), inference(resolution, [status(thm)], [c_674, c_3949])).
% 14.99/8.59  tff(c_3995, plain, (![B_721, B_722]: (k1_relat_1(k7_relat_1(B_721, k4_xboole_0(k1_relat_1(B_721), B_722)))=k4_xboole_0(k1_relat_1(B_721), B_722) | ~v1_relat_1(B_721))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3974])).
% 14.99/8.59  tff(c_80, plain, (![A_49, B_50]: (k6_subset_1(A_49, B_50)=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.99/8.59  tff(c_88, plain, (k1_relat_1(k7_relat_1('#skF_4', k6_subset_1(k1_relat_1('#skF_4'), '#skF_3')))!=k6_subset_1(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.99/8.59  tff(c_91, plain, (k1_relat_1(k7_relat_1('#skF_4', k4_xboole_0(k1_relat_1('#skF_4'), '#skF_3')))!=k4_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_88])).
% 14.99/8.59  tff(c_4050, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3995, c_91])).
% 14.99/8.59  tff(c_4093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_4050])).
% 14.99/8.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.99/8.59  
% 14.99/8.59  Inference rules
% 14.99/8.59  ----------------------
% 14.99/8.59  #Ref     : 0
% 14.99/8.59  #Sup     : 945
% 14.99/8.59  #Fact    : 56
% 14.99/8.59  #Define  : 0
% 14.99/8.59  #Split   : 0
% 14.99/8.59  #Chain   : 0
% 14.99/8.59  #Close   : 0
% 14.99/8.59  
% 14.99/8.59  Ordering : KBO
% 14.99/8.59  
% 14.99/8.59  Simplification rules
% 14.99/8.59  ----------------------
% 14.99/8.59  #Subsume      : 319
% 14.99/8.59  #Demod        : 333
% 14.99/8.59  #Tautology    : 145
% 14.99/8.59  #SimpNegUnit  : 0
% 14.99/8.59  #BackRed      : 0
% 14.99/8.59  
% 14.99/8.59  #Partial instantiations: 0
% 14.99/8.59  #Strategies tried      : 1
% 14.99/8.59  
% 14.99/8.59  Timing (in seconds)
% 14.99/8.59  ----------------------
% 14.99/8.60  Preprocessing        : 0.37
% 14.99/8.60  Parsing              : 0.18
% 14.99/8.60  CNF conversion       : 0.03
% 14.99/8.60  Main loop            : 7.44
% 14.99/8.60  Inferencing          : 0.83
% 14.99/8.60  Reduction            : 0.56
% 14.99/8.60  Demodulation         : 0.46
% 14.99/8.60  BG Simplification    : 0.14
% 14.99/8.60  Subsumption          : 5.80
% 14.99/8.60  Abstraction          : 0.33
% 14.99/8.60  MUC search           : 0.00
% 14.99/8.60  Cooper               : 0.00
% 14.99/8.60  Total                : 7.84
% 14.99/8.60  Index Insertion      : 0.00
% 14.99/8.60  Index Deletion       : 0.00
% 14.99/8.60  Index Matching       : 0.00
% 14.99/8.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
