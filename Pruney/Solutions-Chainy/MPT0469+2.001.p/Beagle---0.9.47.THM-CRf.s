%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:51 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 107 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 152 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_84,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_50,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_31] :
      ( v1_relat_1(A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_158,plain,(
    ! [A_57,B_58,C_59,D_60] : v1_relat_1(k2_tarski(k4_tarski(A_57,B_58),k4_tarski(C_59,D_60))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    ! [A_57,B_58] : v1_relat_1(k1_tarski(k4_tarski(A_57,B_58))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_158])).

tff(c_40,plain,(
    ! [A_18,B_19,C_20,D_21] : v1_relat_1(k2_tarski(k4_tarski(A_18,B_19),k4_tarski(C_20,D_21))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_22,B_23),k4_tarski(C_24,D_25))) = k2_tarski(A_22,C_24)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_22,B_23),k4_tarski(C_24,D_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_178,plain,(
    ! [A_66,B_67,C_68,D_69] : k1_relat_1(k2_tarski(k4_tarski(A_66,B_67),k4_tarski(C_68,D_69))) = k2_tarski(A_66,C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_188,plain,(
    ! [A_66,B_67] : k2_tarski(A_66,A_66) = k1_relat_1(k1_tarski(k4_tarski(A_66,B_67))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_178])).

tff(c_191,plain,(
    ! [A_66,B_67] : k1_relat_1(k1_tarski(k4_tarski(A_66,B_67))) = k1_tarski(A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_188])).

tff(c_221,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_relat_1(A_78),k1_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_230,plain,(
    ! [A_78,A_66,B_67] :
      ( r1_tarski(k1_relat_1(A_78),k1_tarski(A_66))
      | ~ r1_tarski(A_78,k1_tarski(k4_tarski(A_66,B_67)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_66,B_67)))
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_221])).

tff(c_345,plain,(
    ! [A_94,A_95,B_96] :
      ( r1_tarski(k1_relat_1(A_94),k1_tarski(A_95))
      | ~ r1_tarski(A_94,k1_tarski(k4_tarski(A_95,B_96)))
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_230])).

tff(c_351,plain,(
    ! [A_95] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_tarski(A_95))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_345])).

tff(c_356,plain,(
    ! [A_97] : r1_tarski(k1_relat_1(k1_xboole_0),k1_tarski(A_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_351])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_365,plain,(
    ! [A_98] : k4_xboole_0(k1_relat_1(k1_xboole_0),k1_tarski(A_98)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_356,c_8])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,k1_tarski(B_16)) = A_15
      | r2_hidden(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_370,plain,(
    ! [A_98] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | r2_hidden(A_98,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_36])).

tff(c_384,plain,(
    ! [A_99] : r2_hidden(A_99,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_370])).

tff(c_16,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,A_39)
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_90,plain,(
    ! [D_11,B_7] : ~ r2_hidden(k2_tarski(D_11,B_7),D_11) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_402,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_384,c_90])).

tff(c_403,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_473,plain,(
    ! [A_116,B_117,C_118,D_119] : v1_relat_1(k2_tarski(k4_tarski(A_116,B_117),k4_tarski(C_118,D_119))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_477,plain,(
    ! [A_116,B_117] : v1_relat_1(k1_tarski(k4_tarski(A_116,B_117))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_473])).

tff(c_42,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_22,B_23),k4_tarski(C_24,D_25))) = k2_tarski(B_23,D_25)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_22,B_23),k4_tarski(C_24,D_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_510,plain,(
    ! [A_130,B_131,C_132,D_133] : k2_relat_1(k2_tarski(k4_tarski(A_130,B_131),k4_tarski(C_132,D_133))) = k2_tarski(B_131,D_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_520,plain,(
    ! [B_131,A_130] : k2_tarski(B_131,B_131) = k2_relat_1(k1_tarski(k4_tarski(A_130,B_131))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_510])).

tff(c_523,plain,(
    ! [A_130,B_131] : k2_relat_1(k1_tarski(k4_tarski(A_130,B_131))) = k1_tarski(B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_520])).

tff(c_533,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(k2_relat_1(A_136),k2_relat_1(B_137))
      | ~ r1_tarski(A_136,B_137)
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_542,plain,(
    ! [A_136,B_131,A_130] :
      ( r1_tarski(k2_relat_1(A_136),k1_tarski(B_131))
      | ~ r1_tarski(A_136,k1_tarski(k4_tarski(A_130,B_131)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_130,B_131)))
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_533])).

tff(c_769,plain,(
    ! [A_176,B_177,A_178] :
      ( r1_tarski(k2_relat_1(A_176),k1_tarski(B_177))
      | ~ r1_tarski(A_176,k1_tarski(k4_tarski(A_178,B_177)))
      | ~ v1_relat_1(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_542])).

tff(c_775,plain,(
    ! [B_177] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(B_177))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_769])).

tff(c_780,plain,(
    ! [B_179] : r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(B_179)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_775])).

tff(c_793,plain,(
    ! [B_180] : k4_xboole_0(k2_relat_1(k1_xboole_0),k1_tarski(B_180)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_780,c_8])).

tff(c_801,plain,(
    ! [B_180] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | r2_hidden(B_180,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_36])).

tff(c_812,plain,(
    ! [B_181] : r2_hidden(B_181,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_801])).

tff(c_409,plain,(
    ! [B_100,A_101] :
      ( ~ r2_hidden(B_100,A_101)
      | ~ r2_hidden(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_418,plain,(
    ! [D_11,B_7] : ~ r2_hidden(k2_tarski(D_11,B_7),D_11) ),
    inference(resolution,[status(thm)],[c_16,c_409])).

tff(c_835,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_812,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 09:43:19 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 2.70/1.43  
% 2.70/1.43  %Foreground sorts:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Background operators:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Foreground operators:
% 2.70/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.43  
% 2.70/1.45  tff(f_84, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.70/1.45  tff(f_31, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.70/1.45  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.70/1.45  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.70/1.45  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.45  tff(f_61, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.70/1.45  tff(f_69, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 2.70/1.45  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.70/1.45  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.45  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.70/1.45  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.70/1.45  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.70/1.45  tff(c_50, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.70/1.45  tff(c_80, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.70/1.45  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.45  tff(c_56, plain, (![A_31]: (v1_relat_1(A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.70/1.45  tff(c_60, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.70/1.45  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.45  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.45  tff(c_158, plain, (![A_57, B_58, C_59, D_60]: (v1_relat_1(k2_tarski(k4_tarski(A_57, B_58), k4_tarski(C_59, D_60))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.45  tff(c_162, plain, (![A_57, B_58]: (v1_relat_1(k1_tarski(k4_tarski(A_57, B_58))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_158])).
% 2.70/1.45  tff(c_40, plain, (![A_18, B_19, C_20, D_21]: (v1_relat_1(k2_tarski(k4_tarski(A_18, B_19), k4_tarski(C_20, D_21))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.45  tff(c_44, plain, (![A_22, B_23, C_24, D_25]: (k1_relat_1(k2_tarski(k4_tarski(A_22, B_23), k4_tarski(C_24, D_25)))=k2_tarski(A_22, C_24) | ~v1_relat_1(k2_tarski(k4_tarski(A_22, B_23), k4_tarski(C_24, D_25))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.70/1.45  tff(c_178, plain, (![A_66, B_67, C_68, D_69]: (k1_relat_1(k2_tarski(k4_tarski(A_66, B_67), k4_tarski(C_68, D_69)))=k2_tarski(A_66, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 2.70/1.45  tff(c_188, plain, (![A_66, B_67]: (k2_tarski(A_66, A_66)=k1_relat_1(k1_tarski(k4_tarski(A_66, B_67))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_178])).
% 2.70/1.45  tff(c_191, plain, (![A_66, B_67]: (k1_relat_1(k1_tarski(k4_tarski(A_66, B_67)))=k1_tarski(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_188])).
% 2.70/1.45  tff(c_221, plain, (![A_78, B_79]: (r1_tarski(k1_relat_1(A_78), k1_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.45  tff(c_230, plain, (![A_78, A_66, B_67]: (r1_tarski(k1_relat_1(A_78), k1_tarski(A_66)) | ~r1_tarski(A_78, k1_tarski(k4_tarski(A_66, B_67))) | ~v1_relat_1(k1_tarski(k4_tarski(A_66, B_67))) | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_191, c_221])).
% 2.70/1.45  tff(c_345, plain, (![A_94, A_95, B_96]: (r1_tarski(k1_relat_1(A_94), k1_tarski(A_95)) | ~r1_tarski(A_94, k1_tarski(k4_tarski(A_95, B_96))) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_230])).
% 2.70/1.45  tff(c_351, plain, (![A_95]: (r1_tarski(k1_relat_1(k1_xboole_0), k1_tarski(A_95)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_345])).
% 2.70/1.45  tff(c_356, plain, (![A_97]: (r1_tarski(k1_relat_1(k1_xboole_0), k1_tarski(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_351])).
% 2.70/1.45  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.45  tff(c_365, plain, (![A_98]: (k4_xboole_0(k1_relat_1(k1_xboole_0), k1_tarski(A_98))=k1_xboole_0)), inference(resolution, [status(thm)], [c_356, c_8])).
% 2.70/1.45  tff(c_36, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k1_tarski(B_16))=A_15 | r2_hidden(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.45  tff(c_370, plain, (![A_98]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | r2_hidden(A_98, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_365, c_36])).
% 2.70/1.45  tff(c_384, plain, (![A_99]: (r2_hidden(A_99, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_80, c_370])).
% 2.70/1.45  tff(c_16, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.70/1.45  tff(c_81, plain, (![B_38, A_39]: (~r2_hidden(B_38, A_39) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.70/1.45  tff(c_90, plain, (![D_11, B_7]: (~r2_hidden(k2_tarski(D_11, B_7), D_11))), inference(resolution, [status(thm)], [c_16, c_81])).
% 2.70/1.45  tff(c_402, plain, $false, inference(resolution, [status(thm)], [c_384, c_90])).
% 2.70/1.45  tff(c_403, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.70/1.45  tff(c_473, plain, (![A_116, B_117, C_118, D_119]: (v1_relat_1(k2_tarski(k4_tarski(A_116, B_117), k4_tarski(C_118, D_119))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.45  tff(c_477, plain, (![A_116, B_117]: (v1_relat_1(k1_tarski(k4_tarski(A_116, B_117))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_473])).
% 2.70/1.45  tff(c_42, plain, (![A_22, B_23, C_24, D_25]: (k2_relat_1(k2_tarski(k4_tarski(A_22, B_23), k4_tarski(C_24, D_25)))=k2_tarski(B_23, D_25) | ~v1_relat_1(k2_tarski(k4_tarski(A_22, B_23), k4_tarski(C_24, D_25))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.70/1.45  tff(c_510, plain, (![A_130, B_131, C_132, D_133]: (k2_relat_1(k2_tarski(k4_tarski(A_130, B_131), k4_tarski(C_132, D_133)))=k2_tarski(B_131, D_133))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 2.70/1.45  tff(c_520, plain, (![B_131, A_130]: (k2_tarski(B_131, B_131)=k2_relat_1(k1_tarski(k4_tarski(A_130, B_131))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_510])).
% 2.70/1.45  tff(c_523, plain, (![A_130, B_131]: (k2_relat_1(k1_tarski(k4_tarski(A_130, B_131)))=k1_tarski(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_520])).
% 2.70/1.45  tff(c_533, plain, (![A_136, B_137]: (r1_tarski(k2_relat_1(A_136), k2_relat_1(B_137)) | ~r1_tarski(A_136, B_137) | ~v1_relat_1(B_137) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.45  tff(c_542, plain, (![A_136, B_131, A_130]: (r1_tarski(k2_relat_1(A_136), k1_tarski(B_131)) | ~r1_tarski(A_136, k1_tarski(k4_tarski(A_130, B_131))) | ~v1_relat_1(k1_tarski(k4_tarski(A_130, B_131))) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_523, c_533])).
% 2.70/1.45  tff(c_769, plain, (![A_176, B_177, A_178]: (r1_tarski(k2_relat_1(A_176), k1_tarski(B_177)) | ~r1_tarski(A_176, k1_tarski(k4_tarski(A_178, B_177))) | ~v1_relat_1(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_542])).
% 2.70/1.45  tff(c_775, plain, (![B_177]: (r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(B_177)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_769])).
% 2.70/1.45  tff(c_780, plain, (![B_179]: (r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(B_179)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_775])).
% 2.70/1.45  tff(c_793, plain, (![B_180]: (k4_xboole_0(k2_relat_1(k1_xboole_0), k1_tarski(B_180))=k1_xboole_0)), inference(resolution, [status(thm)], [c_780, c_8])).
% 2.70/1.45  tff(c_801, plain, (![B_180]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | r2_hidden(B_180, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_793, c_36])).
% 2.70/1.45  tff(c_812, plain, (![B_181]: (r2_hidden(B_181, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_403, c_801])).
% 2.70/1.45  tff(c_409, plain, (![B_100, A_101]: (~r2_hidden(B_100, A_101) | ~r2_hidden(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.70/1.45  tff(c_418, plain, (![D_11, B_7]: (~r2_hidden(k2_tarski(D_11, B_7), D_11))), inference(resolution, [status(thm)], [c_16, c_409])).
% 2.70/1.45  tff(c_835, plain, $false, inference(resolution, [status(thm)], [c_812, c_418])).
% 2.70/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  Inference rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Ref     : 0
% 2.70/1.45  #Sup     : 166
% 2.70/1.45  #Fact    : 0
% 2.70/1.45  #Define  : 0
% 2.70/1.45  #Split   : 1
% 2.70/1.45  #Chain   : 0
% 2.70/1.45  #Close   : 0
% 2.70/1.45  
% 2.70/1.45  Ordering : KBO
% 2.70/1.45  
% 2.70/1.45  Simplification rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Subsume      : 8
% 2.70/1.45  #Demod        : 63
% 2.70/1.45  #Tautology    : 66
% 2.70/1.45  #SimpNegUnit  : 6
% 2.70/1.45  #BackRed      : 0
% 2.70/1.45  
% 2.70/1.45  #Partial instantiations: 0
% 2.70/1.45  #Strategies tried      : 1
% 2.70/1.45  
% 2.70/1.45  Timing (in seconds)
% 2.70/1.45  ----------------------
% 2.70/1.45  Preprocessing        : 0.30
% 2.70/1.46  Parsing              : 0.16
% 2.70/1.46  CNF conversion       : 0.02
% 2.70/1.46  Main loop            : 0.38
% 2.70/1.46  Inferencing          : 0.16
% 2.70/1.46  Reduction            : 0.12
% 2.70/1.46  Demodulation         : 0.08
% 2.70/1.46  BG Simplification    : 0.02
% 2.70/1.46  Subsumption          : 0.06
% 2.70/1.46  Abstraction          : 0.02
% 2.70/1.46  MUC search           : 0.00
% 2.70/1.46  Cooper               : 0.00
% 2.70/1.46  Total                : 0.72
% 2.70/1.46  Index Insertion      : 0.00
% 2.70/1.46  Index Deletion       : 0.00
% 2.70/1.46  Index Matching       : 0.00
% 2.70/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
