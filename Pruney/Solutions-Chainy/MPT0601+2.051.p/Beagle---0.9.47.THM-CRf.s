%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   73 (  86 expanded)
%              Number of leaves         :   39 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 108 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_356,plain,(
    ! [A_113,B_114] : k3_xboole_0(k1_tarski(A_113),k2_tarski(A_113,B_114)) = k1_tarski(A_113) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_365,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_356])).

tff(c_393,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k3_xboole_0(A_117,B_118)) = k4_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_402,plain,(
    ! [A_7] : k5_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_393])).

tff(c_411,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_402])).

tff(c_28,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_413,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_28])).

tff(c_337,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k1_tarski(A_110),B_111)
      | ~ r2_hidden(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_346,plain,(
    ! [A_110] :
      ( k1_tarski(A_110) = k1_xboole_0
      | ~ r2_hidden(A_110,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_337,c_6])).

tff(c_421,plain,(
    ! [A_110] : ~ r2_hidden(A_110,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_346])).

tff(c_52,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_192,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_279,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski(A_100,B_101),C_102)
      | ~ r2_hidden(B_101,k11_relat_1(C_102,A_100))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [C_51,A_36,D_54] :
      ( r2_hidden(C_51,k1_relat_1(A_36))
      | ~ r2_hidden(k4_tarski(C_51,D_54),A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_294,plain,(
    ! [A_103,C_104,B_105] :
      ( r2_hidden(A_103,k1_relat_1(C_104))
      | ~ r2_hidden(B_105,k11_relat_1(C_104,A_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_279,c_36])).

tff(c_303,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(A_106,k1_relat_1(C_107))
      | ~ v1_relat_1(C_107)
      | k11_relat_1(C_107,A_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_294])).

tff(c_314,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_303,c_108])).

tff(c_319,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_314])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_319])).

tff(c_323,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_322,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_514,plain,(
    ! [C_143,A_144] :
      ( r2_hidden(k4_tarski(C_143,'#skF_5'(A_144,k1_relat_1(A_144),C_143)),A_144)
      | ~ r2_hidden(C_143,k1_relat_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [B_56,C_57,A_55] :
      ( r2_hidden(B_56,k11_relat_1(C_57,A_55))
      | ~ r2_hidden(k4_tarski(A_55,B_56),C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_991,plain,(
    ! [A_188,C_189] :
      ( r2_hidden('#skF_5'(A_188,k1_relat_1(A_188),C_189),k11_relat_1(A_188,C_189))
      | ~ v1_relat_1(A_188)
      | ~ r2_hidden(C_189,k1_relat_1(A_188)) ) ),
    inference(resolution,[status(thm)],[c_514,c_48])).

tff(c_1011,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_991])).

tff(c_1016,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_50,c_1011])).

tff(c_1018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_1016])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.93/1.47  
% 2.93/1.47  %Foreground sorts:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Background operators:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Foreground operators:
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.93/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.93/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.93/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.93/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.93/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.93/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.93/1.47  
% 2.93/1.48  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.93/1.48  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.93/1.48  tff(f_59, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.93/1.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.93/1.48  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.93/1.48  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.93/1.48  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.93/1.48  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.93/1.48  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.93/1.48  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.93/1.48  tff(f_74, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.93/1.48  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.48  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.48  tff(c_356, plain, (![A_113, B_114]: (k3_xboole_0(k1_tarski(A_113), k2_tarski(A_113, B_114))=k1_tarski(A_113))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.93/1.48  tff(c_365, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_356])).
% 2.93/1.48  tff(c_393, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k3_xboole_0(A_117, B_118))=k4_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.48  tff(c_402, plain, (![A_7]: (k5_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_365, c_393])).
% 2.93/1.48  tff(c_411, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_402])).
% 2.93/1.48  tff(c_28, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.93/1.48  tff(c_413, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_28])).
% 2.93/1.48  tff(c_337, plain, (![A_110, B_111]: (r1_tarski(k1_tarski(A_110), B_111) | ~r2_hidden(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.93/1.48  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.48  tff(c_346, plain, (![A_110]: (k1_tarski(A_110)=k1_xboole_0 | ~r2_hidden(A_110, k1_xboole_0))), inference(resolution, [status(thm)], [c_337, c_6])).
% 2.93/1.48  tff(c_421, plain, (![A_110]: (~r2_hidden(A_110, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_413, c_346])).
% 2.93/1.48  tff(c_52, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.48  tff(c_108, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.93/1.48  tff(c_58, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.48  tff(c_192, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_58])).
% 2.93/1.48  tff(c_50, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.48  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.48  tff(c_279, plain, (![A_100, B_101, C_102]: (r2_hidden(k4_tarski(A_100, B_101), C_102) | ~r2_hidden(B_101, k11_relat_1(C_102, A_100)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.93/1.48  tff(c_36, plain, (![C_51, A_36, D_54]: (r2_hidden(C_51, k1_relat_1(A_36)) | ~r2_hidden(k4_tarski(C_51, D_54), A_36))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.48  tff(c_294, plain, (![A_103, C_104, B_105]: (r2_hidden(A_103, k1_relat_1(C_104)) | ~r2_hidden(B_105, k11_relat_1(C_104, A_103)) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_279, c_36])).
% 2.93/1.48  tff(c_303, plain, (![A_106, C_107]: (r2_hidden(A_106, k1_relat_1(C_107)) | ~v1_relat_1(C_107) | k11_relat_1(C_107, A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_294])).
% 2.93/1.48  tff(c_314, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_303, c_108])).
% 2.93/1.48  tff(c_319, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_314])).
% 2.93/1.48  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_319])).
% 2.93/1.48  tff(c_323, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 2.93/1.48  tff(c_322, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.93/1.48  tff(c_514, plain, (![C_143, A_144]: (r2_hidden(k4_tarski(C_143, '#skF_5'(A_144, k1_relat_1(A_144), C_143)), A_144) | ~r2_hidden(C_143, k1_relat_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.48  tff(c_48, plain, (![B_56, C_57, A_55]: (r2_hidden(B_56, k11_relat_1(C_57, A_55)) | ~r2_hidden(k4_tarski(A_55, B_56), C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.93/1.48  tff(c_991, plain, (![A_188, C_189]: (r2_hidden('#skF_5'(A_188, k1_relat_1(A_188), C_189), k11_relat_1(A_188, C_189)) | ~v1_relat_1(A_188) | ~r2_hidden(C_189, k1_relat_1(A_188)))), inference(resolution, [status(thm)], [c_514, c_48])).
% 2.93/1.48  tff(c_1011, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_991])).
% 2.93/1.48  tff(c_1016, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_323, c_50, c_1011])).
% 2.93/1.48  tff(c_1018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_1016])).
% 2.93/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.48  
% 2.93/1.48  Inference rules
% 2.93/1.48  ----------------------
% 2.93/1.48  #Ref     : 0
% 2.93/1.48  #Sup     : 210
% 2.93/1.48  #Fact    : 0
% 2.93/1.48  #Define  : 0
% 2.93/1.48  #Split   : 3
% 2.93/1.48  #Chain   : 0
% 2.93/1.48  #Close   : 0
% 2.93/1.48  
% 2.93/1.48  Ordering : KBO
% 2.93/1.48  
% 2.93/1.48  Simplification rules
% 2.93/1.48  ----------------------
% 2.93/1.48  #Subsume      : 28
% 2.93/1.48  #Demod        : 80
% 2.93/1.48  #Tautology    : 103
% 2.93/1.48  #SimpNegUnit  : 32
% 2.93/1.48  #BackRed      : 5
% 2.93/1.48  
% 2.93/1.48  #Partial instantiations: 0
% 2.93/1.48  #Strategies tried      : 1
% 2.93/1.48  
% 2.93/1.48  Timing (in seconds)
% 2.93/1.48  ----------------------
% 2.93/1.48  Preprocessing        : 0.32
% 2.93/1.48  Parsing              : 0.16
% 2.93/1.48  CNF conversion       : 0.02
% 2.93/1.48  Main loop            : 0.36
% 3.14/1.48  Inferencing          : 0.13
% 3.14/1.48  Reduction            : 0.11
% 3.14/1.48  Demodulation         : 0.07
% 3.14/1.48  BG Simplification    : 0.02
% 3.14/1.48  Subsumption          : 0.06
% 3.14/1.48  Abstraction          : 0.02
% 3.14/1.48  MUC search           : 0.00
% 3.14/1.48  Cooper               : 0.00
% 3.14/1.48  Total                : 0.70
% 3.14/1.48  Index Insertion      : 0.00
% 3.14/1.48  Index Deletion       : 0.00
% 3.14/1.48  Index Matching       : 0.00
% 3.14/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
