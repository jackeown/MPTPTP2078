%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:24 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   73 (  91 expanded)
%              Number of leaves         :   41 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  82 expanded)
%              Number of equality atoms :   38 (  51 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_78,axiom,(
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

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_38,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43),A_43)
      | v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden(A_72,B_73)
      | ~ r1_xboole_0(k1_tarski(A_72),B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_130,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_124])).

tff(c_135,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_130])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_175,plain,(
    ! [A_83] :
      ( k10_relat_1(A_83,k2_relat_1(A_83)) = k1_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_184,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_175])).

tff(c_188,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_46,c_184])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k4_xboole_0(B_88,A_87)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_240,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_228])).

tff(c_244,plain,(
    ! [A_89] : k2_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_240])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_250,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,A_89) = A_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_2])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_205,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_208,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_205])).

tff(c_237,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = k2_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_228])).

tff(c_317,plain,(
    ! [A_94] : k5_xboole_0(k1_xboole_0,A_94) = A_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_237])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_328,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_4])).

tff(c_350,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_328])).

tff(c_356,plain,(
    ! [B_95,A_96] :
      ( k10_relat_1(B_95,k3_xboole_0(k2_relat_1(B_95),A_96)) = k10_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_373,plain,(
    ! [A_96] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_96)) = k10_relat_1(k1_xboole_0,A_96)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_356])).

tff(c_378,plain,(
    ! [A_96] : k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_96)) = k10_relat_1(k1_xboole_0,A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_373])).

tff(c_399,plain,(
    ! [A_96] : k10_relat_1(k1_xboole_0,A_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_350,c_378])).

tff(c_48,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.16/1.26  
% 2.16/1.26  %Foreground sorts:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Background operators:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Foreground operators:
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.26  
% 2.27/1.27  tff(f_70, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.27/1.27  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.27/1.27  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.27/1.27  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.27/1.27  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.27/1.27  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.27/1.27  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.27/1.27  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.27/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.27/1.27  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.27/1.27  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.27/1.27  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.27/1.27  tff(f_84, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.27/1.27  tff(c_38, plain, (![A_43]: (r2_hidden('#skF_1'(A_43), A_43) | v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.27  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.27  tff(c_124, plain, (![A_72, B_73]: (~r2_hidden(A_72, B_73) | ~r1_xboole_0(k1_tarski(A_72), B_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.27  tff(c_130, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_124])).
% 2.27/1.27  tff(c_135, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_130])).
% 2.27/1.27  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.27/1.27  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.27/1.27  tff(c_175, plain, (![A_83]: (k10_relat_1(A_83, k2_relat_1(A_83))=k1_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.27  tff(c_184, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_175])).
% 2.27/1.27  tff(c_188, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_46, c_184])).
% 2.27/1.27  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.27  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.27  tff(c_228, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k4_xboole_0(B_88, A_87))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.27  tff(c_240, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_228])).
% 2.27/1.27  tff(c_244, plain, (![A_89]: (k2_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_240])).
% 2.27/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.27  tff(c_250, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, A_89)=A_89)), inference(superposition, [status(thm), theory('equality')], [c_244, c_2])).
% 2.27/1.27  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.27  tff(c_193, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.27  tff(c_205, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_193])).
% 2.27/1.27  tff(c_208, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_205])).
% 2.27/1.27  tff(c_237, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=k2_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_208, c_228])).
% 2.27/1.27  tff(c_317, plain, (![A_94]: (k5_xboole_0(k1_xboole_0, A_94)=A_94)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_237])).
% 2.27/1.27  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.27  tff(c_328, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_317, c_4])).
% 2.27/1.27  tff(c_350, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_328])).
% 2.27/1.27  tff(c_356, plain, (![B_95, A_96]: (k10_relat_1(B_95, k3_xboole_0(k2_relat_1(B_95), A_96))=k10_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.27/1.27  tff(c_373, plain, (![A_96]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_96))=k10_relat_1(k1_xboole_0, A_96) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_356])).
% 2.27/1.27  tff(c_378, plain, (![A_96]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_96))=k10_relat_1(k1_xboole_0, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_373])).
% 2.27/1.27  tff(c_399, plain, (![A_96]: (k10_relat_1(k1_xboole_0, A_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_350, c_378])).
% 2.27/1.27  tff(c_48, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.27  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_48])).
% 2.27/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  
% 2.27/1.27  Inference rules
% 2.27/1.27  ----------------------
% 2.27/1.27  #Ref     : 0
% 2.27/1.27  #Sup     : 82
% 2.27/1.27  #Fact    : 0
% 2.27/1.27  #Define  : 0
% 2.27/1.27  #Split   : 0
% 2.27/1.27  #Chain   : 0
% 2.27/1.27  #Close   : 0
% 2.27/1.27  
% 2.27/1.27  Ordering : KBO
% 2.27/1.27  
% 2.27/1.27  Simplification rules
% 2.27/1.27  ----------------------
% 2.27/1.27  #Subsume      : 0
% 2.27/1.27  #Demod        : 26
% 2.27/1.27  #Tautology    : 71
% 2.27/1.27  #SimpNegUnit  : 0
% 2.27/1.27  #BackRed      : 1
% 2.27/1.27  
% 2.27/1.27  #Partial instantiations: 0
% 2.27/1.27  #Strategies tried      : 1
% 2.27/1.27  
% 2.27/1.27  Timing (in seconds)
% 2.27/1.27  ----------------------
% 2.27/1.27  Preprocessing        : 0.32
% 2.27/1.27  Parsing              : 0.17
% 2.27/1.27  CNF conversion       : 0.02
% 2.27/1.27  Main loop            : 0.18
% 2.27/1.27  Inferencing          : 0.07
% 2.27/1.27  Reduction            : 0.06
% 2.27/1.27  Demodulation         : 0.05
% 2.27/1.27  BG Simplification    : 0.02
% 2.27/1.27  Subsumption          : 0.02
% 2.27/1.27  Abstraction          : 0.01
% 2.27/1.27  MUC search           : 0.00
% 2.27/1.27  Cooper               : 0.00
% 2.27/1.27  Total                : 0.53
% 2.27/1.27  Index Insertion      : 0.00
% 2.27/1.27  Index Deletion       : 0.00
% 2.27/1.27  Index Matching       : 0.00
% 2.27/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
