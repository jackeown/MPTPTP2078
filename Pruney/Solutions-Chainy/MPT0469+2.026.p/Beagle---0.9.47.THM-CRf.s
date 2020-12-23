%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 104 expanded)
%              Number of leaves         :   43 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 108 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_54,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_87,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_71,plain,(
    ! [A_67] :
      ( v1_relat_1(A_67)
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_52,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_6'(A_62,B_63),k2_relat_1(B_63))
      | ~ r2_hidden(A_62,k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_210,plain,(
    ! [A_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_5'(A_101,k2_relat_1(A_101),C_102),C_102),A_101)
      | ~ r2_hidden(C_102,k2_relat_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [A_39] : k1_setfam_1(k1_tarski(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    ! [A_77,B_78] : k1_setfam_1(k2_tarski(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_116,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_119,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_116])).

tff(c_138,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_147,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_138])).

tff(c_150,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_30,plain,(
    ! [B_38] : k4_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) != k1_tarski(B_38) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_151,plain,(
    ! [B_38] : k1_tarski(B_38) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_30])).

tff(c_90,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [A_74] :
      ( k1_tarski(A_74) = k1_xboole_0
      | ~ r2_hidden(A_74,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_90,c_8])).

tff(c_168,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_99])).

tff(c_220,plain,(
    ! [C_103] : ~ r2_hidden(C_103,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_210,c_168])).

tff(c_228,plain,(
    ! [A_62] :
      ( ~ r2_hidden(A_62,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_220])).

tff(c_263,plain,(
    ! [A_109] : ~ r2_hidden(A_109,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_228])).

tff(c_271,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_263])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_271])).

tff(c_277,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_414,plain,(
    ! [A_145,C_146] :
      ( r2_hidden(k4_tarski('#skF_5'(A_145,k2_relat_1(A_145),C_146),C_146),A_145)
      | ~ r2_hidden(C_146,k2_relat_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_310,plain,(
    ! [A_117,B_118] : k1_setfam_1(k2_tarski(A_117,B_118)) = k3_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_319,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_310])).

tff(c_322,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_319])).

tff(c_333,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k3_xboole_0(A_121,B_122)) = k4_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_342,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_333])).

tff(c_345,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_342])).

tff(c_346,plain,(
    ! [B_38] : k1_tarski(B_38) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_30])).

tff(c_283,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k1_tarski(A_110),B_111)
      | ~ r2_hidden(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_288,plain,(
    ! [A_110] :
      ( k1_tarski(A_110) = k1_xboole_0
      | ~ r2_hidden(A_110,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_283,c_8])).

tff(c_354,plain,(
    ! [A_110] : ~ r2_hidden(A_110,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_288])).

tff(c_424,plain,(
    ! [C_147] : ~ r2_hidden(C_147,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_414,c_354])).

tff(c_436,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_424])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.47/1.38  
% 2.47/1.38  %Foreground sorts:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Background operators:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Foreground operators:
% 2.47/1.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.47/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.47/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.38  
% 2.47/1.39  tff(f_94, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.47/1.39  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.47/1.39  tff(f_73, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.47/1.39  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.47/1.39  tff(f_81, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.47/1.39  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.47/1.39  tff(f_67, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.47/1.39  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.39  tff(f_69, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.47/1.39  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.47/1.39  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.47/1.39  tff(f_60, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.47/1.39  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.47/1.39  tff(c_54, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.39  tff(c_87, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 2.47/1.39  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.47/1.39  tff(c_71, plain, (![A_67]: (v1_relat_1(A_67) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.39  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.47/1.39  tff(c_52, plain, (![A_62, B_63]: (r2_hidden('#skF_6'(A_62, B_63), k2_relat_1(B_63)) | ~r2_hidden(A_62, k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.47/1.39  tff(c_210, plain, (![A_101, C_102]: (r2_hidden(k4_tarski('#skF_5'(A_101, k2_relat_1(A_101), C_102), C_102), A_101) | ~r2_hidden(C_102, k2_relat_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.47/1.39  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.47/1.39  tff(c_34, plain, (![A_39]: (k1_setfam_1(k1_tarski(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.39  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.39  tff(c_107, plain, (![A_77, B_78]: (k1_setfam_1(k2_tarski(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.39  tff(c_116, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_107])).
% 2.47/1.39  tff(c_119, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_116])).
% 2.47/1.39  tff(c_138, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.39  tff(c_147, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_119, c_138])).
% 2.47/1.39  tff(c_150, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_147])).
% 2.47/1.39  tff(c_30, plain, (![B_38]: (k4_xboole_0(k1_tarski(B_38), k1_tarski(B_38))!=k1_tarski(B_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.39  tff(c_151, plain, (![B_38]: (k1_tarski(B_38)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_30])).
% 2.47/1.39  tff(c_90, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.47/1.39  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.47/1.39  tff(c_99, plain, (![A_74]: (k1_tarski(A_74)=k1_xboole_0 | ~r2_hidden(A_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_8])).
% 2.47/1.39  tff(c_168, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_151, c_99])).
% 2.47/1.39  tff(c_220, plain, (![C_103]: (~r2_hidden(C_103, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_210, c_168])).
% 2.47/1.39  tff(c_228, plain, (![A_62]: (~r2_hidden(A_62, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_220])).
% 2.47/1.39  tff(c_263, plain, (![A_109]: (~r2_hidden(A_109, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_228])).
% 2.47/1.39  tff(c_271, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_263])).
% 2.47/1.39  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_271])).
% 2.47/1.39  tff(c_277, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.47/1.39  tff(c_414, plain, (![A_145, C_146]: (r2_hidden(k4_tarski('#skF_5'(A_145, k2_relat_1(A_145), C_146), C_146), A_145) | ~r2_hidden(C_146, k2_relat_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.47/1.39  tff(c_310, plain, (![A_117, B_118]: (k1_setfam_1(k2_tarski(A_117, B_118))=k3_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.39  tff(c_319, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_310])).
% 2.47/1.39  tff(c_322, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_319])).
% 2.47/1.39  tff(c_333, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k3_xboole_0(A_121, B_122))=k4_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.39  tff(c_342, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_322, c_333])).
% 2.47/1.39  tff(c_345, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_342])).
% 2.47/1.39  tff(c_346, plain, (![B_38]: (k1_tarski(B_38)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_30])).
% 2.47/1.39  tff(c_283, plain, (![A_110, B_111]: (r1_tarski(k1_tarski(A_110), B_111) | ~r2_hidden(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.47/1.39  tff(c_288, plain, (![A_110]: (k1_tarski(A_110)=k1_xboole_0 | ~r2_hidden(A_110, k1_xboole_0))), inference(resolution, [status(thm)], [c_283, c_8])).
% 2.47/1.39  tff(c_354, plain, (![A_110]: (~r2_hidden(A_110, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_346, c_288])).
% 2.47/1.39  tff(c_424, plain, (![C_147]: (~r2_hidden(C_147, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_414, c_354])).
% 2.47/1.39  tff(c_436, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_424])).
% 2.47/1.39  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_436])).
% 2.47/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  Inference rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Ref     : 0
% 2.47/1.39  #Sup     : 77
% 2.47/1.39  #Fact    : 0
% 2.47/1.39  #Define  : 0
% 2.47/1.39  #Split   : 1
% 2.47/1.39  #Chain   : 0
% 2.47/1.39  #Close   : 0
% 2.47/1.39  
% 2.47/1.39  Ordering : KBO
% 2.47/1.39  
% 2.47/1.39  Simplification rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Subsume      : 3
% 2.47/1.39  #Demod        : 12
% 2.47/1.39  #Tautology    : 58
% 2.47/1.39  #SimpNegUnit  : 10
% 2.47/1.39  #BackRed      : 5
% 2.47/1.39  
% 2.47/1.39  #Partial instantiations: 0
% 2.47/1.39  #Strategies tried      : 1
% 2.47/1.39  
% 2.47/1.39  Timing (in seconds)
% 2.47/1.39  ----------------------
% 2.47/1.40  Preprocessing        : 0.37
% 2.47/1.40  Parsing              : 0.19
% 2.47/1.40  CNF conversion       : 0.03
% 2.47/1.40  Main loop            : 0.20
% 2.47/1.40  Inferencing          : 0.08
% 2.47/1.40  Reduction            : 0.06
% 2.47/1.40  Demodulation         : 0.04
% 2.47/1.40  BG Simplification    : 0.02
% 2.47/1.40  Subsumption          : 0.03
% 2.47/1.40  Abstraction          : 0.01
% 2.47/1.40  MUC search           : 0.00
% 2.47/1.40  Cooper               : 0.00
% 2.47/1.40  Total                : 0.60
% 2.47/1.40  Index Insertion      : 0.00
% 2.47/1.40  Index Deletion       : 0.00
% 2.47/1.40  Index Matching       : 0.00
% 2.47/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
