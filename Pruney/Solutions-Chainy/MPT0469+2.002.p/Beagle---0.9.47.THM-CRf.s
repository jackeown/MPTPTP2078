%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:51 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 109 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 152 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_64,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_116,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_71,plain,(
    ! [B_42] : k2_zfmisc_1(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_48])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_198,plain,(
    ! [A_71,B_72,C_73,D_74] : v1_relat_1(k2_tarski(k4_tarski(A_71,B_72),k4_tarski(C_73,D_74))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_202,plain,(
    ! [A_71,B_72] : v1_relat_1(k1_tarski(k4_tarski(A_71,B_72))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_198])).

tff(c_50,plain,(
    ! [A_26,B_27,C_28,D_29] : v1_relat_1(k2_tarski(k4_tarski(A_26,B_27),k4_tarski(C_28,D_29))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_30,B_31),k4_tarski(C_32,D_33))) = k2_tarski(A_30,C_32)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_30,B_31),k4_tarski(C_32,D_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_304,plain,(
    ! [A_98,B_99,C_100,D_101] : k1_relat_1(k2_tarski(k4_tarski(A_98,B_99),k4_tarski(C_100,D_101))) = k2_tarski(A_98,C_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_314,plain,(
    ! [A_98,B_99] : k2_tarski(A_98,A_98) = k1_relat_1(k1_tarski(k4_tarski(A_98,B_99))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_304])).

tff(c_317,plain,(
    ! [A_98,B_99] : k1_relat_1(k1_tarski(k4_tarski(A_98,B_99))) = k1_tarski(A_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_314])).

tff(c_327,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_relat_1(A_104),k1_relat_1(B_105))
      | ~ r1_tarski(A_104,B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_339,plain,(
    ! [A_104,A_98,B_99] :
      ( r1_tarski(k1_relat_1(A_104),k1_tarski(A_98))
      | ~ r1_tarski(A_104,k1_tarski(k4_tarski(A_98,B_99)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_98,B_99)))
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_327])).

tff(c_517,plain,(
    ! [A_123,A_124,B_125] :
      ( r1_tarski(k1_relat_1(A_123),k1_tarski(A_124))
      | ~ r1_tarski(A_123,k1_tarski(k4_tarski(A_124,B_125)))
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_339])).

tff(c_523,plain,(
    ! [A_124] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_tarski(A_124))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_517])).

tff(c_528,plain,(
    ! [A_126] : r1_tarski(k1_relat_1(k1_xboole_0),k1_tarski(A_126)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_523])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_542,plain,(
    ! [A_130] : k4_xboole_0(k1_relat_1(k1_xboole_0),k1_tarski(A_130)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_528,c_6])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,k1_tarski(B_22)) = A_21
      | r2_hidden(B_22,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_550,plain,(
    ! [A_130] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | r2_hidden(A_130,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_44])).

tff(c_565,plain,(
    ! [A_131] : r2_hidden(A_131,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_550])).

tff(c_16,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden(B_53,A_54)
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_129,plain,(
    ! [A_10,D_15] : ~ r2_hidden(k2_tarski(A_10,D_15),D_15) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_588,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_565,c_129])).

tff(c_589,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_726,plain,(
    ! [A_161,B_162,C_163,D_164] : v1_relat_1(k2_tarski(k4_tarski(A_161,B_162),k4_tarski(C_163,D_164))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_730,plain,(
    ! [A_161,B_162] : v1_relat_1(k1_tarski(k4_tarski(A_161,B_162))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_726])).

tff(c_52,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_30,B_31),k4_tarski(C_32,D_33))) = k2_tarski(B_31,D_33)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_30,B_31),k4_tarski(C_32,D_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_761,plain,(
    ! [A_174,B_175,C_176,D_177] : k2_relat_1(k2_tarski(k4_tarski(A_174,B_175),k4_tarski(C_176,D_177))) = k2_tarski(B_175,D_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_771,plain,(
    ! [B_175,A_174] : k2_tarski(B_175,B_175) = k2_relat_1(k1_tarski(k4_tarski(A_174,B_175))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_761])).

tff(c_774,plain,(
    ! [A_174,B_175] : k2_relat_1(k1_tarski(k4_tarski(A_174,B_175))) = k1_tarski(B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_771])).

tff(c_1047,plain,(
    ! [A_204,B_205] :
      ( r1_tarski(k2_relat_1(A_204),k2_relat_1(B_205))
      | ~ r1_tarski(A_204,B_205)
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1059,plain,(
    ! [A_204,B_175,A_174] :
      ( r1_tarski(k2_relat_1(A_204),k1_tarski(B_175))
      | ~ r1_tarski(A_204,k1_tarski(k4_tarski(A_174,B_175)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_174,B_175)))
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_1047])).

tff(c_1214,plain,(
    ! [A_232,B_233,A_234] :
      ( r1_tarski(k2_relat_1(A_232),k1_tarski(B_233))
      | ~ r1_tarski(A_232,k1_tarski(k4_tarski(A_234,B_233)))
      | ~ v1_relat_1(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_1059])).

tff(c_1220,plain,(
    ! [B_233] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(B_233))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1214])).

tff(c_1235,plain,(
    ! [B_239] : r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(B_239)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1220])).

tff(c_1252,plain,(
    ! [B_240] : k4_xboole_0(k2_relat_1(k1_xboole_0),k1_tarski(B_240)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1235,c_6])).

tff(c_1260,plain,(
    ! [B_240] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | r2_hidden(B_240,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_44])).

tff(c_1275,plain,(
    ! [B_241] : r2_hidden(B_241,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_1260])).

tff(c_598,plain,(
    ! [B_135,A_136] :
      ( ~ r2_hidden(B_135,A_136)
      | ~ r2_hidden(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_607,plain,(
    ! [A_10,D_15] : ~ r2_hidden(k2_tarski(A_10,D_15),D_15) ),
    inference(resolution,[status(thm)],[c_16,c_598])).

tff(c_1293,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1275,c_607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.72  
% 3.44/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.72  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.44/1.72  
% 3.44/1.72  %Foreground sorts:
% 3.44/1.72  
% 3.44/1.72  
% 3.44/1.72  %Background operators:
% 3.44/1.72  
% 3.44/1.72  
% 3.44/1.72  %Foreground operators:
% 3.44/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.44/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.44/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.44/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.72  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.44/1.72  
% 3.44/1.74  tff(f_105, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.44/1.74  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.44/1.74  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.44/1.74  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.44/1.74  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.74  tff(f_76, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 3.44/1.74  tff(f_84, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 3.44/1.74  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.44/1.74  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.44/1.74  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.44/1.74  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.44/1.74  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.44/1.74  tff(c_64, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.44/1.74  tff(c_116, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 3.44/1.74  tff(c_71, plain, (![B_42]: (k2_zfmisc_1(k1_xboole_0, B_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.74  tff(c_48, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.44/1.74  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_71, c_48])).
% 3.44/1.74  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.74  tff(c_32, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.74  tff(c_198, plain, (![A_71, B_72, C_73, D_74]: (v1_relat_1(k2_tarski(k4_tarski(A_71, B_72), k4_tarski(C_73, D_74))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.74  tff(c_202, plain, (![A_71, B_72]: (v1_relat_1(k1_tarski(k4_tarski(A_71, B_72))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_198])).
% 3.44/1.74  tff(c_50, plain, (![A_26, B_27, C_28, D_29]: (v1_relat_1(k2_tarski(k4_tarski(A_26, B_27), k4_tarski(C_28, D_29))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.74  tff(c_54, plain, (![A_30, B_31, C_32, D_33]: (k1_relat_1(k2_tarski(k4_tarski(A_30, B_31), k4_tarski(C_32, D_33)))=k2_tarski(A_30, C_32) | ~v1_relat_1(k2_tarski(k4_tarski(A_30, B_31), k4_tarski(C_32, D_33))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.74  tff(c_304, plain, (![A_98, B_99, C_100, D_101]: (k1_relat_1(k2_tarski(k4_tarski(A_98, B_99), k4_tarski(C_100, D_101)))=k2_tarski(A_98, C_100))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54])).
% 3.44/1.74  tff(c_314, plain, (![A_98, B_99]: (k2_tarski(A_98, A_98)=k1_relat_1(k1_tarski(k4_tarski(A_98, B_99))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_304])).
% 3.44/1.74  tff(c_317, plain, (![A_98, B_99]: (k1_relat_1(k1_tarski(k4_tarski(A_98, B_99)))=k1_tarski(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_314])).
% 3.44/1.74  tff(c_327, plain, (![A_104, B_105]: (r1_tarski(k1_relat_1(A_104), k1_relat_1(B_105)) | ~r1_tarski(A_104, B_105) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.44/1.74  tff(c_339, plain, (![A_104, A_98, B_99]: (r1_tarski(k1_relat_1(A_104), k1_tarski(A_98)) | ~r1_tarski(A_104, k1_tarski(k4_tarski(A_98, B_99))) | ~v1_relat_1(k1_tarski(k4_tarski(A_98, B_99))) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_317, c_327])).
% 3.44/1.74  tff(c_517, plain, (![A_123, A_124, B_125]: (r1_tarski(k1_relat_1(A_123), k1_tarski(A_124)) | ~r1_tarski(A_123, k1_tarski(k4_tarski(A_124, B_125))) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_339])).
% 3.44/1.74  tff(c_523, plain, (![A_124]: (r1_tarski(k1_relat_1(k1_xboole_0), k1_tarski(A_124)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_517])).
% 3.44/1.74  tff(c_528, plain, (![A_126]: (r1_tarski(k1_relat_1(k1_xboole_0), k1_tarski(A_126)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_523])).
% 3.44/1.74  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.74  tff(c_542, plain, (![A_130]: (k4_xboole_0(k1_relat_1(k1_xboole_0), k1_tarski(A_130))=k1_xboole_0)), inference(resolution, [status(thm)], [c_528, c_6])).
% 3.44/1.74  tff(c_44, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k1_tarski(B_22))=A_21 | r2_hidden(B_22, A_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.74  tff(c_550, plain, (![A_130]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | r2_hidden(A_130, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_542, c_44])).
% 3.44/1.74  tff(c_565, plain, (![A_131]: (r2_hidden(A_131, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_116, c_550])).
% 3.44/1.74  tff(c_16, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.74  tff(c_120, plain, (![B_53, A_54]: (~r2_hidden(B_53, A_54) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.44/1.74  tff(c_129, plain, (![A_10, D_15]: (~r2_hidden(k2_tarski(A_10, D_15), D_15))), inference(resolution, [status(thm)], [c_16, c_120])).
% 3.44/1.74  tff(c_588, plain, $false, inference(resolution, [status(thm)], [c_565, c_129])).
% 3.44/1.74  tff(c_589, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 3.44/1.74  tff(c_726, plain, (![A_161, B_162, C_163, D_164]: (v1_relat_1(k2_tarski(k4_tarski(A_161, B_162), k4_tarski(C_163, D_164))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.74  tff(c_730, plain, (![A_161, B_162]: (v1_relat_1(k1_tarski(k4_tarski(A_161, B_162))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_726])).
% 3.44/1.74  tff(c_52, plain, (![A_30, B_31, C_32, D_33]: (k2_relat_1(k2_tarski(k4_tarski(A_30, B_31), k4_tarski(C_32, D_33)))=k2_tarski(B_31, D_33) | ~v1_relat_1(k2_tarski(k4_tarski(A_30, B_31), k4_tarski(C_32, D_33))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.74  tff(c_761, plain, (![A_174, B_175, C_176, D_177]: (k2_relat_1(k2_tarski(k4_tarski(A_174, B_175), k4_tarski(C_176, D_177)))=k2_tarski(B_175, D_177))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 3.44/1.74  tff(c_771, plain, (![B_175, A_174]: (k2_tarski(B_175, B_175)=k2_relat_1(k1_tarski(k4_tarski(A_174, B_175))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_761])).
% 3.44/1.74  tff(c_774, plain, (![A_174, B_175]: (k2_relat_1(k1_tarski(k4_tarski(A_174, B_175)))=k1_tarski(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_771])).
% 3.44/1.74  tff(c_1047, plain, (![A_204, B_205]: (r1_tarski(k2_relat_1(A_204), k2_relat_1(B_205)) | ~r1_tarski(A_204, B_205) | ~v1_relat_1(B_205) | ~v1_relat_1(A_204))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.44/1.74  tff(c_1059, plain, (![A_204, B_175, A_174]: (r1_tarski(k2_relat_1(A_204), k1_tarski(B_175)) | ~r1_tarski(A_204, k1_tarski(k4_tarski(A_174, B_175))) | ~v1_relat_1(k1_tarski(k4_tarski(A_174, B_175))) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_774, c_1047])).
% 3.44/1.74  tff(c_1214, plain, (![A_232, B_233, A_234]: (r1_tarski(k2_relat_1(A_232), k1_tarski(B_233)) | ~r1_tarski(A_232, k1_tarski(k4_tarski(A_234, B_233))) | ~v1_relat_1(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_1059])).
% 3.44/1.74  tff(c_1220, plain, (![B_233]: (r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(B_233)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1214])).
% 3.44/1.74  tff(c_1235, plain, (![B_239]: (r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(B_239)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1220])).
% 3.44/1.74  tff(c_1252, plain, (![B_240]: (k4_xboole_0(k2_relat_1(k1_xboole_0), k1_tarski(B_240))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1235, c_6])).
% 3.44/1.74  tff(c_1260, plain, (![B_240]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | r2_hidden(B_240, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_44])).
% 3.44/1.74  tff(c_1275, plain, (![B_241]: (r2_hidden(B_241, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_589, c_1260])).
% 3.44/1.74  tff(c_598, plain, (![B_135, A_136]: (~r2_hidden(B_135, A_136) | ~r2_hidden(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.44/1.74  tff(c_607, plain, (![A_10, D_15]: (~r2_hidden(k2_tarski(A_10, D_15), D_15))), inference(resolution, [status(thm)], [c_16, c_598])).
% 3.44/1.74  tff(c_1293, plain, $false, inference(resolution, [status(thm)], [c_1275, c_607])).
% 3.44/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.74  
% 3.44/1.74  Inference rules
% 3.44/1.74  ----------------------
% 3.44/1.74  #Ref     : 0
% 3.44/1.74  #Sup     : 266
% 3.44/1.74  #Fact    : 0
% 3.44/1.74  #Define  : 0
% 3.44/1.74  #Split   : 1
% 3.44/1.74  #Chain   : 0
% 3.44/1.74  #Close   : 0
% 3.44/1.74  
% 3.44/1.74  Ordering : KBO
% 3.44/1.74  
% 3.44/1.74  Simplification rules
% 3.44/1.74  ----------------------
% 3.44/1.74  #Subsume      : 9
% 3.44/1.74  #Demod        : 93
% 3.44/1.74  #Tautology    : 112
% 3.44/1.74  #SimpNegUnit  : 10
% 3.44/1.74  #BackRed      : 0
% 3.44/1.74  
% 3.44/1.74  #Partial instantiations: 0
% 3.44/1.74  #Strategies tried      : 1
% 3.44/1.74  
% 3.44/1.74  Timing (in seconds)
% 3.44/1.74  ----------------------
% 3.44/1.74  Preprocessing        : 0.39
% 3.44/1.74  Parsing              : 0.22
% 3.44/1.74  CNF conversion       : 0.03
% 3.44/1.74  Main loop            : 0.46
% 3.44/1.74  Inferencing          : 0.18
% 3.44/1.74  Reduction            : 0.14
% 3.44/1.74  Demodulation         : 0.09
% 3.44/1.74  BG Simplification    : 0.03
% 3.44/1.74  Subsumption          : 0.08
% 3.44/1.74  Abstraction          : 0.02
% 3.44/1.74  MUC search           : 0.00
% 3.44/1.74  Cooper               : 0.00
% 3.44/1.74  Total                : 0.89
% 3.44/1.74  Index Insertion      : 0.00
% 3.44/1.74  Index Deletion       : 0.00
% 3.44/1.74  Index Matching       : 0.00
% 3.44/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
