%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 223 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  104 ( 347 expanded)
%              Number of equality atoms :   37 ( 149 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_40,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_21] : v1_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_264,plain,(
    ! [B_71,A_72] : k5_relat_1(k6_relat_1(B_71),k6_relat_1(A_72)) = k6_relat_1(k3_xboole_0(A_72,B_71)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_270,plain,(
    ! [A_72,B_71] :
      ( k7_relat_1(k6_relat_1(A_72),B_71) = k6_relat_1(k3_xboole_0(A_72,B_71))
      | ~ v1_relat_1(k6_relat_1(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_26])).

tff(c_280,plain,(
    ! [A_72,B_71] : k7_relat_1(k6_relat_1(A_72),B_71) = k6_relat_1(k3_xboole_0(A_72,B_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_270])).

tff(c_24,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_284,plain,(
    ! [A_73,B_74] : k7_relat_1(k6_relat_1(A_73),B_74) = k6_relat_1(k3_xboole_0(A_73,B_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_270])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_290,plain,(
    ! [A_73,B_74] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_73,B_74))) = k9_relat_1(k6_relat_1(A_73),B_74)
      | ~ v1_relat_1(k6_relat_1(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_18])).

tff(c_296,plain,(
    ! [A_73,B_74] : k9_relat_1(k6_relat_1(A_73),B_74) = k3_xboole_0(A_73,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_290])).

tff(c_741,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,k9_relat_1(B_118,k1_relat_1(B_118))) = k9_relat_1(B_118,k10_relat_1(B_118,A_117))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_825,plain,(
    ! [A_18,A_117] :
      ( k9_relat_1(k6_relat_1(A_18),k10_relat_1(k6_relat_1(A_18),A_117)) = k3_xboole_0(A_117,k9_relat_1(k6_relat_1(A_18),A_18))
      | ~ v1_funct_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_741])).

tff(c_836,plain,(
    ! [A_119,A_120] : k3_xboole_0(A_119,k10_relat_1(k6_relat_1(A_119),A_120)) = k3_xboole_0(A_120,A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_296,c_296,c_825])).

tff(c_32,plain,(
    ! [A_22,C_24,B_23] :
      ( k3_xboole_0(A_22,k10_relat_1(C_24,B_23)) = k10_relat_1(k7_relat_1(C_24,A_22),B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_874,plain,(
    ! [A_119,A_120] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_119),A_119),A_120) = k3_xboole_0(A_120,A_119)
      | ~ v1_relat_1(k6_relat_1(A_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_32])).

tff(c_921,plain,(
    ! [A_119,A_120] : k10_relat_1(k6_relat_1(A_119),A_120) = k3_xboole_0(A_120,A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_280,c_874])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1102,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_tarski(A_132,k10_relat_1(C_133,B_134))
      | ~ r1_tarski(k9_relat_1(C_133,A_132),B_134)
      | ~ r1_tarski(A_132,k1_relat_1(C_133))
      | ~ v1_funct_1(C_133)
      | ~ v1_relat_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2528,plain,(
    ! [A_200,C_201] :
      ( r1_tarski(A_200,k10_relat_1(C_201,k9_relat_1(C_201,A_200)))
      | ~ r1_tarski(A_200,k1_relat_1(C_201))
      | ~ v1_funct_1(C_201)
      | ~ v1_relat_1(C_201) ) ),
    inference(resolution,[status(thm)],[c_8,c_1102])).

tff(c_2550,plain,(
    ! [B_74,A_73] :
      ( r1_tarski(B_74,k10_relat_1(k6_relat_1(A_73),k3_xboole_0(A_73,B_74)))
      | ~ r1_tarski(B_74,k1_relat_1(k6_relat_1(A_73)))
      | ~ v1_funct_1(k6_relat_1(A_73))
      | ~ v1_relat_1(k6_relat_1(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_2528])).

tff(c_2787,plain,(
    ! [B_212,A_213] :
      ( r1_tarski(B_212,k3_xboole_0(k3_xboole_0(A_213,B_212),A_213))
      | ~ r1_tarski(B_212,A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_22,c_921,c_2550])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [A_50,A_5,B_6] :
      ( r1_tarski(A_50,A_5)
      | ~ r1_tarski(A_50,k3_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_2849,plain,(
    ! [B_214,A_215] :
      ( r1_tarski(B_214,k3_xboole_0(A_215,B_214))
      | ~ r1_tarski(B_214,A_215) ) ),
    inference(resolution,[status(thm)],[c_2787,c_133])).

tff(c_835,plain,(
    ! [A_18,A_117] : k3_xboole_0(A_18,k10_relat_1(k6_relat_1(A_18),A_117)) = k3_xboole_0(A_117,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_296,c_296,c_825])).

tff(c_101,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k3_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_889,plain,(
    ! [A_119,A_120] :
      ( k3_xboole_0(A_119,k10_relat_1(k6_relat_1(A_119),A_120)) = A_119
      | ~ r1_tarski(A_119,k3_xboole_0(A_120,A_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_108])).

tff(c_922,plain,(
    ! [A_120,A_119] :
      ( k3_xboole_0(A_120,A_119) = A_119
      | ~ r1_tarski(A_119,k3_xboole_0(A_120,A_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_889])).

tff(c_2914,plain,(
    ! [A_216,B_217] :
      ( k3_xboole_0(A_216,B_217) = B_217
      | ~ r1_tarski(B_217,A_216) ) ),
    inference(resolution,[status(thm)],[c_2849,c_922])).

tff(c_3055,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_2914])).

tff(c_3173,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3055,c_32])).

tff(c_3215,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3173])).

tff(c_3217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.72  
% 4.17/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.72  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.17/1.72  
% 4.17/1.72  %Foreground sorts:
% 4.17/1.72  
% 4.17/1.72  
% 4.17/1.72  %Background operators:
% 4.17/1.72  
% 4.17/1.72  
% 4.17/1.72  %Foreground operators:
% 4.17/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.17/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.17/1.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.17/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.17/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.17/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.17/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.17/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.17/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.17/1.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.17/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.17/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.17/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.17/1.72  
% 4.17/1.74  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 4.17/1.74  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.17/1.74  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.17/1.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.17/1.74  tff(f_87, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.17/1.74  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.17/1.74  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.17/1.74  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 4.17/1.74  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.17/1.74  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.17/1.74  tff(f_85, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.17/1.74  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.17/1.74  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.17/1.74  tff(c_40, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.17/1.74  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.17/1.74  tff(c_42, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.17/1.74  tff(c_28, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.17/1.74  tff(c_30, plain, (![A_21]: (v1_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.17/1.74  tff(c_22, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.17/1.74  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.17/1.74  tff(c_264, plain, (![B_71, A_72]: (k5_relat_1(k6_relat_1(B_71), k6_relat_1(A_72))=k6_relat_1(k3_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.74  tff(c_26, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.17/1.74  tff(c_270, plain, (![A_72, B_71]: (k7_relat_1(k6_relat_1(A_72), B_71)=k6_relat_1(k3_xboole_0(A_72, B_71)) | ~v1_relat_1(k6_relat_1(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_26])).
% 4.17/1.74  tff(c_280, plain, (![A_72, B_71]: (k7_relat_1(k6_relat_1(A_72), B_71)=k6_relat_1(k3_xboole_0(A_72, B_71)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_270])).
% 4.17/1.74  tff(c_24, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.17/1.74  tff(c_284, plain, (![A_73, B_74]: (k7_relat_1(k6_relat_1(A_73), B_74)=k6_relat_1(k3_xboole_0(A_73, B_74)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_270])).
% 4.17/1.74  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.17/1.74  tff(c_290, plain, (![A_73, B_74]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_73, B_74)))=k9_relat_1(k6_relat_1(A_73), B_74) | ~v1_relat_1(k6_relat_1(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_18])).
% 4.17/1.74  tff(c_296, plain, (![A_73, B_74]: (k9_relat_1(k6_relat_1(A_73), B_74)=k3_xboole_0(A_73, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_290])).
% 4.17/1.74  tff(c_741, plain, (![A_117, B_118]: (k3_xboole_0(A_117, k9_relat_1(B_118, k1_relat_1(B_118)))=k9_relat_1(B_118, k10_relat_1(B_118, A_117)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.17/1.74  tff(c_825, plain, (![A_18, A_117]: (k9_relat_1(k6_relat_1(A_18), k10_relat_1(k6_relat_1(A_18), A_117))=k3_xboole_0(A_117, k9_relat_1(k6_relat_1(A_18), A_18)) | ~v1_funct_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_741])).
% 4.17/1.74  tff(c_836, plain, (![A_119, A_120]: (k3_xboole_0(A_119, k10_relat_1(k6_relat_1(A_119), A_120))=k3_xboole_0(A_120, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_296, c_296, c_825])).
% 4.17/1.74  tff(c_32, plain, (![A_22, C_24, B_23]: (k3_xboole_0(A_22, k10_relat_1(C_24, B_23))=k10_relat_1(k7_relat_1(C_24, A_22), B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.17/1.74  tff(c_874, plain, (![A_119, A_120]: (k10_relat_1(k7_relat_1(k6_relat_1(A_119), A_119), A_120)=k3_xboole_0(A_120, A_119) | ~v1_relat_1(k6_relat_1(A_119)))), inference(superposition, [status(thm), theory('equality')], [c_836, c_32])).
% 4.17/1.74  tff(c_921, plain, (![A_119, A_120]: (k10_relat_1(k6_relat_1(A_119), A_120)=k3_xboole_0(A_120, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_280, c_874])).
% 4.17/1.74  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.17/1.74  tff(c_1102, plain, (![A_132, C_133, B_134]: (r1_tarski(A_132, k10_relat_1(C_133, B_134)) | ~r1_tarski(k9_relat_1(C_133, A_132), B_134) | ~r1_tarski(A_132, k1_relat_1(C_133)) | ~v1_funct_1(C_133) | ~v1_relat_1(C_133))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.17/1.74  tff(c_2528, plain, (![A_200, C_201]: (r1_tarski(A_200, k10_relat_1(C_201, k9_relat_1(C_201, A_200))) | ~r1_tarski(A_200, k1_relat_1(C_201)) | ~v1_funct_1(C_201) | ~v1_relat_1(C_201))), inference(resolution, [status(thm)], [c_8, c_1102])).
% 4.17/1.74  tff(c_2550, plain, (![B_74, A_73]: (r1_tarski(B_74, k10_relat_1(k6_relat_1(A_73), k3_xboole_0(A_73, B_74))) | ~r1_tarski(B_74, k1_relat_1(k6_relat_1(A_73))) | ~v1_funct_1(k6_relat_1(A_73)) | ~v1_relat_1(k6_relat_1(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_296, c_2528])).
% 4.17/1.74  tff(c_2787, plain, (![B_212, A_213]: (r1_tarski(B_212, k3_xboole_0(k3_xboole_0(A_213, B_212), A_213)) | ~r1_tarski(B_212, A_213))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_22, c_921, c_2550])).
% 4.17/1.74  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.17/1.74  tff(c_123, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.17/1.74  tff(c_133, plain, (![A_50, A_5, B_6]: (r1_tarski(A_50, A_5) | ~r1_tarski(A_50, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_123])).
% 4.17/1.74  tff(c_2849, plain, (![B_214, A_215]: (r1_tarski(B_214, k3_xboole_0(A_215, B_214)) | ~r1_tarski(B_214, A_215))), inference(resolution, [status(thm)], [c_2787, c_133])).
% 4.17/1.74  tff(c_835, plain, (![A_18, A_117]: (k3_xboole_0(A_18, k10_relat_1(k6_relat_1(A_18), A_117))=k3_xboole_0(A_117, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_296, c_296, c_825])).
% 4.17/1.74  tff(c_101, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.17/1.74  tff(c_108, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_101])).
% 4.17/1.74  tff(c_889, plain, (![A_119, A_120]: (k3_xboole_0(A_119, k10_relat_1(k6_relat_1(A_119), A_120))=A_119 | ~r1_tarski(A_119, k3_xboole_0(A_120, A_119)))), inference(superposition, [status(thm), theory('equality')], [c_836, c_108])).
% 4.17/1.74  tff(c_922, plain, (![A_120, A_119]: (k3_xboole_0(A_120, A_119)=A_119 | ~r1_tarski(A_119, k3_xboole_0(A_120, A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_889])).
% 4.17/1.74  tff(c_2914, plain, (![A_216, B_217]: (k3_xboole_0(A_216, B_217)=B_217 | ~r1_tarski(B_217, A_216))), inference(resolution, [status(thm)], [c_2849, c_922])).
% 4.17/1.74  tff(c_3055, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_2914])).
% 4.17/1.74  tff(c_3173, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3055, c_32])).
% 4.17/1.74  tff(c_3215, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3173])).
% 4.17/1.74  tff(c_3217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_3215])).
% 4.17/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.74  
% 4.17/1.74  Inference rules
% 4.17/1.74  ----------------------
% 4.17/1.74  #Ref     : 0
% 4.17/1.74  #Sup     : 723
% 4.17/1.74  #Fact    : 0
% 4.17/1.74  #Define  : 0
% 4.17/1.74  #Split   : 1
% 4.17/1.74  #Chain   : 0
% 4.17/1.74  #Close   : 0
% 4.17/1.74  
% 4.17/1.74  Ordering : KBO
% 4.17/1.74  
% 4.17/1.74  Simplification rules
% 4.17/1.74  ----------------------
% 4.17/1.74  #Subsume      : 24
% 4.17/1.74  #Demod        : 439
% 4.17/1.74  #Tautology    : 305
% 4.17/1.74  #SimpNegUnit  : 1
% 4.17/1.74  #BackRed      : 12
% 4.17/1.74  
% 4.17/1.74  #Partial instantiations: 0
% 4.17/1.74  #Strategies tried      : 1
% 4.17/1.74  
% 4.17/1.74  Timing (in seconds)
% 4.17/1.74  ----------------------
% 4.17/1.74  Preprocessing        : 0.31
% 4.17/1.74  Parsing              : 0.17
% 4.17/1.74  CNF conversion       : 0.02
% 4.17/1.74  Main loop            : 0.67
% 4.17/1.74  Inferencing          : 0.21
% 4.17/1.74  Reduction            : 0.24
% 4.17/1.74  Demodulation         : 0.18
% 4.17/1.74  BG Simplification    : 0.03
% 4.17/1.74  Subsumption          : 0.13
% 4.17/1.74  Abstraction          : 0.05
% 4.17/1.74  MUC search           : 0.00
% 4.17/1.74  Cooper               : 0.00
% 4.17/1.74  Total                : 1.01
% 4.17/1.74  Index Insertion      : 0.00
% 4.17/1.74  Index Deletion       : 0.00
% 4.17/1.74  Index Matching       : 0.00
% 4.17/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
