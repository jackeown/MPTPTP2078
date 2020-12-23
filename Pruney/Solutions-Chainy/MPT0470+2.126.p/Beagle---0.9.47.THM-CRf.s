%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 137 expanded)
%              Number of leaves         :   41 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 222 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    '#skF_5': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_121,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_80,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    ! [A_6,C_86] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_113])).

tff(c_124,plain,(
    ! [C_87] : ~ r2_hidden(C_87,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_120])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_36,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(k5_relat_1(A_58,B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_194,plain,(
    ! [A_113,B_114] :
      ( k1_relat_1(k5_relat_1(A_113,B_114)) = k1_relat_1(A_113)
      | ~ r1_tarski(k2_relat_1(A_113),k1_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_200,plain,(
    ! [B_114] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_114)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_194])).

tff(c_205,plain,(
    ! [B_115] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_115)) = k1_xboole_0
      | ~ v1_relat_1(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_10,c_48,c_200])).

tff(c_38,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k1_relat_1(A_60))
      | ~ v1_relat_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_214,plain,(
    ! [B_115] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_115))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_115))
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_38])).

tff(c_222,plain,(
    ! [B_116] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_116))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_116))
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_70,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | B_71 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_2,c_70])).

tff(c_230,plain,(
    ! [B_117] :
      ( k5_relat_1(k1_xboole_0,B_117) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_222,c_73])).

tff(c_234,plain,(
    ! [B_59] :
      ( k5_relat_1(k1_xboole_0,B_59) = k1_xboole_0
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_230])).

tff(c_238,plain,(
    ! [B_118] :
      ( k5_relat_1(k1_xboole_0,B_118) = k1_xboole_0
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_234])).

tff(c_250,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_250])).

tff(c_258,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_296,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | ~ r2_hidden(C_131,k3_xboole_0(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_303,plain,(
    ! [A_6,C_131] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_131,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_296])).

tff(c_307,plain,(
    ! [C_132] : ~ r2_hidden(C_132,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_303])).

tff(c_312,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_307])).

tff(c_450,plain,(
    ! [B_169,A_170] :
      ( k2_relat_1(k5_relat_1(B_169,A_170)) = k2_relat_1(A_170)
      | ~ r1_tarski(k1_relat_1(A_170),k2_relat_1(B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_456,plain,(
    ! [B_169] :
      ( k2_relat_1(k5_relat_1(B_169,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_450])).

tff(c_503,plain,(
    ! [B_172] :
      ( k2_relat_1(k5_relat_1(B_172,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_10,c_46,c_456])).

tff(c_40,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(k2_relat_1(A_61))
      | ~ v1_relat_1(A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_515,plain,(
    ! [B_172] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_172,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_172,k1_xboole_0))
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_40])).

tff(c_557,plain,(
    ! [B_175] :
      ( ~ v1_relat_1(k5_relat_1(B_175,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_175,k1_xboole_0))
      | ~ v1_relat_1(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_515])).

tff(c_579,plain,(
    ! [B_183] :
      ( k5_relat_1(B_183,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_183,k1_xboole_0))
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_557,c_73])).

tff(c_586,plain,(
    ! [A_58] :
      ( k5_relat_1(A_58,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_36,c_579])).

tff(c_592,plain,(
    ! [A_184] :
      ( k5_relat_1(A_184,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_586])).

tff(c_604,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_592])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.39  
% 2.54/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.54/1.40  
% 2.54/1.40  %Foreground sorts:
% 2.54/1.40  
% 2.54/1.40  
% 2.54/1.40  %Background operators:
% 2.54/1.40  
% 2.54/1.40  
% 2.54/1.40  %Foreground operators:
% 2.54/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.54/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.54/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.40  
% 2.54/1.41  tff(f_128, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.54/1.41  tff(f_78, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.54/1.41  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.54/1.41  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.54/1.41  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.54/1.41  tff(f_84, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.54/1.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.54/1.41  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.54/1.41  tff(f_121, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.54/1.41  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.54/1.41  tff(f_92, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.54/1.41  tff(f_54, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.54/1.41  tff(f_118, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.54/1.41  tff(f_100, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.54/1.41  tff(c_50, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.54/1.41  tff(c_80, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.54/1.41  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.54/1.41  tff(c_34, plain, (![A_40]: (r2_hidden('#skF_2'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.54/1.41  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.54/1.41  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.54/1.41  tff(c_113, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.54/1.41  tff(c_120, plain, (![A_6, C_86]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_113])).
% 2.54/1.41  tff(c_124, plain, (![C_87]: (~r2_hidden(C_87, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_120])).
% 2.54/1.41  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_124])).
% 2.54/1.41  tff(c_36, plain, (![A_58, B_59]: (v1_relat_1(k5_relat_1(A_58, B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.54/1.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.54/1.41  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.54/1.41  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.54/1.41  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.54/1.41  tff(c_194, plain, (![A_113, B_114]: (k1_relat_1(k5_relat_1(A_113, B_114))=k1_relat_1(A_113) | ~r1_tarski(k2_relat_1(A_113), k1_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.54/1.41  tff(c_200, plain, (![B_114]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_114))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_194])).
% 2.54/1.41  tff(c_205, plain, (![B_115]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_115))=k1_xboole_0 | ~v1_relat_1(B_115))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_10, c_48, c_200])).
% 2.54/1.41  tff(c_38, plain, (![A_60]: (~v1_xboole_0(k1_relat_1(A_60)) | ~v1_relat_1(A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.41  tff(c_214, plain, (![B_115]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_115)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_115)) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_205, c_38])).
% 2.54/1.41  tff(c_222, plain, (![B_116]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_116)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_116)) | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_214])).
% 2.54/1.41  tff(c_70, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | B_71=A_72 | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.41  tff(c_73, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_2, c_70])).
% 2.54/1.41  tff(c_230, plain, (![B_117]: (k5_relat_1(k1_xboole_0, B_117)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_117)) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_222, c_73])).
% 2.54/1.41  tff(c_234, plain, (![B_59]: (k5_relat_1(k1_xboole_0, B_59)=k1_xboole_0 | ~v1_relat_1(B_59) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_230])).
% 2.54/1.41  tff(c_238, plain, (![B_118]: (k5_relat_1(k1_xboole_0, B_118)=k1_xboole_0 | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_234])).
% 2.54/1.41  tff(c_250, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_238])).
% 2.54/1.41  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_250])).
% 2.54/1.41  tff(c_258, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.54/1.41  tff(c_296, plain, (![A_129, B_130, C_131]: (~r1_xboole_0(A_129, B_130) | ~r2_hidden(C_131, k3_xboole_0(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.54/1.41  tff(c_303, plain, (![A_6, C_131]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_296])).
% 2.54/1.41  tff(c_307, plain, (![C_132]: (~r2_hidden(C_132, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_303])).
% 2.54/1.41  tff(c_312, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_307])).
% 2.54/1.41  tff(c_450, plain, (![B_169, A_170]: (k2_relat_1(k5_relat_1(B_169, A_170))=k2_relat_1(A_170) | ~r1_tarski(k1_relat_1(A_170), k2_relat_1(B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.54/1.41  tff(c_456, plain, (![B_169]: (k2_relat_1(k5_relat_1(B_169, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_450])).
% 2.54/1.41  tff(c_503, plain, (![B_172]: (k2_relat_1(k5_relat_1(B_172, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_172))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_10, c_46, c_456])).
% 2.54/1.41  tff(c_40, plain, (![A_61]: (~v1_xboole_0(k2_relat_1(A_61)) | ~v1_relat_1(A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.54/1.41  tff(c_515, plain, (![B_172]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_172, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_172, k1_xboole_0)) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_503, c_40])).
% 2.54/1.41  tff(c_557, plain, (![B_175]: (~v1_relat_1(k5_relat_1(B_175, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_175, k1_xboole_0)) | ~v1_relat_1(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_515])).
% 2.54/1.41  tff(c_579, plain, (![B_183]: (k5_relat_1(B_183, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_183, k1_xboole_0)) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_557, c_73])).
% 2.54/1.41  tff(c_586, plain, (![A_58]: (k5_relat_1(A_58, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_36, c_579])).
% 2.54/1.41  tff(c_592, plain, (![A_184]: (k5_relat_1(A_184, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_586])).
% 2.54/1.41  tff(c_604, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_592])).
% 2.54/1.41  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_604])).
% 2.54/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.41  
% 2.54/1.41  Inference rules
% 2.54/1.41  ----------------------
% 2.54/1.41  #Ref     : 2
% 2.54/1.41  #Sup     : 117
% 2.54/1.41  #Fact    : 0
% 2.54/1.41  #Define  : 0
% 2.54/1.41  #Split   : 1
% 2.54/1.41  #Chain   : 0
% 2.54/1.41  #Close   : 0
% 2.54/1.41  
% 2.54/1.41  Ordering : KBO
% 2.54/1.41  
% 2.54/1.41  Simplification rules
% 2.54/1.41  ----------------------
% 2.54/1.41  #Subsume      : 3
% 2.54/1.41  #Demod        : 74
% 2.54/1.41  #Tautology    : 75
% 2.54/1.41  #SimpNegUnit  : 4
% 2.54/1.41  #BackRed      : 0
% 2.54/1.41  
% 2.54/1.41  #Partial instantiations: 0
% 2.54/1.41  #Strategies tried      : 1
% 2.54/1.41  
% 2.54/1.41  Timing (in seconds)
% 2.54/1.41  ----------------------
% 2.54/1.41  Preprocessing        : 0.31
% 2.54/1.42  Parsing              : 0.17
% 2.54/1.42  CNF conversion       : 0.02
% 2.54/1.42  Main loop            : 0.27
% 2.54/1.42  Inferencing          : 0.11
% 2.54/1.42  Reduction            : 0.08
% 2.54/1.42  Demodulation         : 0.05
% 2.54/1.42  BG Simplification    : 0.02
% 2.54/1.42  Subsumption          : 0.04
% 2.54/1.42  Abstraction          : 0.02
% 2.54/1.42  MUC search           : 0.00
% 2.54/1.42  Cooper               : 0.00
% 2.54/1.42  Total                : 0.62
% 2.54/1.42  Index Insertion      : 0.00
% 2.54/1.42  Index Deletion       : 0.00
% 2.54/1.42  Index Matching       : 0.00
% 2.54/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
