%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:24 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   71 (  89 expanded)
%              Number of leaves         :   40 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  81 expanded)
%              Number of equality atoms :   37 (  50 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_36,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43),A_43)
      | v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [A_78,C_79,B_80] :
      ( ~ r2_hidden(A_78,C_79)
      | ~ r1_xboole_0(k2_tarski(A_78,B_80),C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_143,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_176,plain,(
    ! [A_85] :
      ( k10_relat_1(A_85,k2_relat_1(A_85)) = k1_relat_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_185,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_176])).

tff(c_189,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_44,c_185])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k4_xboole_0(B_87,A_86)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_206,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_194])).

tff(c_210,plain,(
    ! [A_88] : k2_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_216,plain,(
    ! [A_88] : k2_xboole_0(k1_xboole_0,A_88) = A_88 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_2])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_153,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_156,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_153])).

tff(c_203,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = k2_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_194])).

tff(c_283,plain,(
    ! [A_93] : k5_xboole_0(k1_xboole_0,A_93) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_203])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_4])).

tff(c_316,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_294])).

tff(c_342,plain,(
    ! [B_95,A_96] :
      ( k10_relat_1(B_95,k3_xboole_0(k2_relat_1(B_95),A_96)) = k10_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_355,plain,(
    ! [A_96] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_96)) = k10_relat_1(k1_xboole_0,A_96)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_342])).

tff(c_360,plain,(
    ! [A_96] : k10_relat_1(k1_xboole_0,A_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_189,c_316,c_355])).

tff(c_46,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.12/1.27  
% 2.12/1.27  %Foreground sorts:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Background operators:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Foreground operators:
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.12/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.27  
% 2.12/1.29  tff(f_68, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.12/1.29  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.29  tff(f_56, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.12/1.29  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.29  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.12/1.29  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.12/1.29  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.12/1.29  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.12/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.12/1.29  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.29  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.12/1.29  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.12/1.29  tff(f_82, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.12/1.29  tff(c_36, plain, (![A_43]: (r2_hidden('#skF_1'(A_43), A_43) | v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.29  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.29  tff(c_132, plain, (![A_78, C_79, B_80]: (~r2_hidden(A_78, C_79) | ~r1_xboole_0(k2_tarski(A_78, B_80), C_79))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.29  tff(c_138, plain, (![A_81]: (~r2_hidden(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_132])).
% 2.12/1.29  tff(c_143, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_138])).
% 2.12/1.29  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_176, plain, (![A_85]: (k10_relat_1(A_85, k2_relat_1(A_85))=k1_relat_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.29  tff(c_185, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_176])).
% 2.12/1.29  tff(c_189, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_44, c_185])).
% 2.12/1.29  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.29  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.29  tff(c_194, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k4_xboole_0(B_87, A_86))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.29  tff(c_206, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_194])).
% 2.12/1.29  tff(c_210, plain, (![A_88]: (k2_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_206])).
% 2.12/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.29  tff(c_216, plain, (![A_88]: (k2_xboole_0(k1_xboole_0, A_88)=A_88)), inference(superposition, [status(thm), theory('equality')], [c_210, c_2])).
% 2.12/1.29  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.29  tff(c_144, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.29  tff(c_153, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 2.12/1.29  tff(c_156, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_153])).
% 2.12/1.29  tff(c_203, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=k2_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_156, c_194])).
% 2.12/1.29  tff(c_283, plain, (![A_93]: (k5_xboole_0(k1_xboole_0, A_93)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_216, c_203])).
% 2.12/1.29  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.29  tff(c_294, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_283, c_4])).
% 2.12/1.29  tff(c_316, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_294])).
% 2.12/1.29  tff(c_342, plain, (![B_95, A_96]: (k10_relat_1(B_95, k3_xboole_0(k2_relat_1(B_95), A_96))=k10_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.29  tff(c_355, plain, (![A_96]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_96))=k10_relat_1(k1_xboole_0, A_96) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_342])).
% 2.12/1.29  tff(c_360, plain, (![A_96]: (k10_relat_1(k1_xboole_0, A_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_189, c_316, c_355])).
% 2.12/1.29  tff(c_46, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.12/1.29  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_360, c_46])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 0
% 2.12/1.29  #Sup     : 73
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 0
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 0
% 2.12/1.29  #Demod        : 26
% 2.12/1.29  #Tautology    : 65
% 2.12/1.29  #SimpNegUnit  : 0
% 2.12/1.29  #BackRed      : 1
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.29  Preprocessing        : 0.34
% 2.12/1.29  Parsing              : 0.18
% 2.12/1.29  CNF conversion       : 0.02
% 2.12/1.29  Main loop            : 0.18
% 2.12/1.29  Inferencing          : 0.07
% 2.12/1.29  Reduction            : 0.06
% 2.12/1.29  Demodulation         : 0.05
% 2.12/1.29  BG Simplification    : 0.02
% 2.12/1.29  Subsumption          : 0.02
% 2.12/1.29  Abstraction          : 0.01
% 2.12/1.29  MUC search           : 0.00
% 2.12/1.29  Cooper               : 0.00
% 2.12/1.29  Total                : 0.55
% 2.12/1.29  Index Insertion      : 0.00
% 2.12/1.29  Index Deletion       : 0.00
% 2.12/1.29  Index Matching       : 0.00
% 2.12/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
