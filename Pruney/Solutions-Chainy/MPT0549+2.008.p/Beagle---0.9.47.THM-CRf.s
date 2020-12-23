%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 153 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 256 expanded)
%              Number of equality atoms :   32 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_491,plain,(
    ! [B_117,A_118] :
      ( r1_xboole_0(k1_relat_1(B_117),A_118)
      | k7_relat_1(B_117,A_118) != k1_xboole_0
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,(
    k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_28,plain,(
    ! [A_40] :
      ( v1_xboole_0(k2_relat_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [A_51] :
      ( v1_xboole_0(k2_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_52,c_6])).

tff(c_83,plain,(
    ! [A_59] :
      ( k2_relat_1(k2_relat_1(A_59)) = k1_xboole_0
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_92,plain,(
    ! [A_59] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_28])).

tff(c_112,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(k2_relat_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_119,plain,(
    ! [A_40] : ~ v1_xboole_0(A_40) ),
    inference(resolution,[status(thm)],[c_28,c_112])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_68] : r2_hidden('#skF_1'(A_68),A_68) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_4])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    ! [A_64,C_65,B_66] :
      ( ~ r2_hidden(A_64,C_65)
      | ~ r1_xboole_0(k2_tarski(A_64,B_66),C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,(
    ! [A_64] : ~ r2_hidden(A_64,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_135,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_130,c_128])).

tff(c_136,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_56,plain,(
    ! [A_51] :
      ( k2_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_52,c_6])).

tff(c_143,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_56])).

tff(c_48,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_48])).

tff(c_209,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,A_83) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_215,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_209])).

tff(c_223,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_215])).

tff(c_34,plain,(
    ! [B_45,A_44] :
      ( k2_relat_1(k7_relat_1(B_45,A_44)) = k9_relat_1(B_45,A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_231,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_34])).

tff(c_240,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_143,c_231])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_240])).

tff(c_243,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_497,plain,
    ( k7_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_491,c_243])).

tff(c_501,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_497])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k7_relat_1(A_38,B_39))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_244,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_385,plain,(
    ! [A_108,B_109] :
      ( k8_relat_1(A_108,B_109) = B_109
      | ~ r1_tarski(k2_relat_1(B_109),A_108)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_787,plain,(
    ! [A_159,B_160,A_161] :
      ( k8_relat_1(A_159,k7_relat_1(B_160,A_161)) = k7_relat_1(B_160,A_161)
      | ~ r1_tarski(k9_relat_1(B_160,A_161),A_159)
      | ~ v1_relat_1(k7_relat_1(B_160,A_161))
      | ~ v1_relat_1(B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_385])).

tff(c_799,plain,(
    ! [A_159] :
      ( k8_relat_1(A_159,k7_relat_1('#skF_3','#skF_2')) = k7_relat_1('#skF_3','#skF_2')
      | ~ r1_tarski(k1_xboole_0,A_159)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_787])).

tff(c_807,plain,(
    ! [A_159] :
      ( k8_relat_1(A_159,k7_relat_1('#skF_3','#skF_2')) = k7_relat_1('#skF_3','#skF_2')
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_799])).

tff(c_808,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_807])).

tff(c_811,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_808])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_811])).

tff(c_898,plain,(
    ! [A_162] : k8_relat_1(A_162,k7_relat_1('#skF_3','#skF_2')) = k7_relat_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_807])).

tff(c_817,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_807])).

tff(c_32,plain,(
    ! [A_43] :
      ( k8_relat_1(k1_xboole_0,A_43) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_825,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_817,c_32])).

tff(c_902,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_825])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:33:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.72/1.40  
% 2.72/1.40  %Foreground sorts:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Background operators:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Foreground operators:
% 2.72/1.40  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.72/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.72/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.72/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.40  
% 2.72/1.41  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.72/1.41  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.72/1.41  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.72/1.41  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.72/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.72/1.41  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.72/1.41  tff(f_56, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.72/1.41  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.72/1.41  tff(f_60, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.72/1.41  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.41  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.72/1.41  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.72/1.41  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.41  tff(c_491, plain, (![B_117, A_118]: (r1_xboole_0(k1_relat_1(B_117), A_118) | k7_relat_1(B_117, A_118)!=k1_xboole_0 | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.72/1.41  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.41  tff(c_72, plain, (k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.72/1.41  tff(c_28, plain, (![A_40]: (v1_xboole_0(k2_relat_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.41  tff(c_52, plain, (![A_51]: (v1_xboole_0(k2_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.41  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.41  tff(c_58, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_52, c_6])).
% 2.72/1.41  tff(c_83, plain, (![A_59]: (k2_relat_1(k2_relat_1(A_59))=k1_xboole_0 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_28, c_58])).
% 2.72/1.41  tff(c_92, plain, (![A_59]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_59)) | ~v1_xboole_0(A_59))), inference(superposition, [status(thm), theory('equality')], [c_83, c_28])).
% 2.72/1.41  tff(c_112, plain, (![A_62]: (~v1_xboole_0(k2_relat_1(A_62)) | ~v1_xboole_0(A_62))), inference(splitLeft, [status(thm)], [c_92])).
% 2.72/1.41  tff(c_119, plain, (![A_40]: (~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_28, c_112])).
% 2.72/1.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.41  tff(c_130, plain, (![A_68]: (r2_hidden('#skF_1'(A_68), A_68))), inference(negUnitSimplification, [status(thm)], [c_119, c_4])).
% 2.72/1.41  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.41  tff(c_123, plain, (![A_64, C_65, B_66]: (~r2_hidden(A_64, C_65) | ~r1_xboole_0(k2_tarski(A_64, B_66), C_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.41  tff(c_128, plain, (![A_64]: (~r2_hidden(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_123])).
% 2.72/1.41  tff(c_135, plain, $false, inference(resolution, [status(thm)], [c_130, c_128])).
% 2.72/1.41  tff(c_136, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_92])).
% 2.72/1.41  tff(c_56, plain, (![A_51]: (k2_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_52, c_6])).
% 2.72/1.41  tff(c_143, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_56])).
% 2.72/1.41  tff(c_48, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.41  tff(c_110, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_48])).
% 2.72/1.41  tff(c_209, plain, (![B_82, A_83]: (k7_relat_1(B_82, A_83)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.72/1.41  tff(c_215, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_110, c_209])).
% 2.72/1.41  tff(c_223, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_215])).
% 2.72/1.41  tff(c_34, plain, (![B_45, A_44]: (k2_relat_1(k7_relat_1(B_45, A_44))=k9_relat_1(B_45, A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.41  tff(c_231, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_223, c_34])).
% 2.72/1.41  tff(c_240, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_143, c_231])).
% 2.72/1.41  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_240])).
% 2.72/1.41  tff(c_243, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.72/1.41  tff(c_497, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_491, c_243])).
% 2.72/1.41  tff(c_501, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_497])).
% 2.72/1.41  tff(c_26, plain, (![A_38, B_39]: (v1_relat_1(k7_relat_1(A_38, B_39)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.41  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.41  tff(c_244, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.72/1.41  tff(c_385, plain, (![A_108, B_109]: (k8_relat_1(A_108, B_109)=B_109 | ~r1_tarski(k2_relat_1(B_109), A_108) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.41  tff(c_787, plain, (![A_159, B_160, A_161]: (k8_relat_1(A_159, k7_relat_1(B_160, A_161))=k7_relat_1(B_160, A_161) | ~r1_tarski(k9_relat_1(B_160, A_161), A_159) | ~v1_relat_1(k7_relat_1(B_160, A_161)) | ~v1_relat_1(B_160))), inference(superposition, [status(thm), theory('equality')], [c_34, c_385])).
% 2.72/1.41  tff(c_799, plain, (![A_159]: (k8_relat_1(A_159, k7_relat_1('#skF_3', '#skF_2'))=k7_relat_1('#skF_3', '#skF_2') | ~r1_tarski(k1_xboole_0, A_159) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_787])).
% 2.72/1.41  tff(c_807, plain, (![A_159]: (k8_relat_1(A_159, k7_relat_1('#skF_3', '#skF_2'))=k7_relat_1('#skF_3', '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_799])).
% 2.72/1.41  tff(c_808, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_807])).
% 2.72/1.41  tff(c_811, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_808])).
% 2.72/1.41  tff(c_815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_811])).
% 2.72/1.41  tff(c_898, plain, (![A_162]: (k8_relat_1(A_162, k7_relat_1('#skF_3', '#skF_2'))=k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_807])).
% 2.72/1.41  tff(c_817, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_807])).
% 2.72/1.41  tff(c_32, plain, (![A_43]: (k8_relat_1(k1_xboole_0, A_43)=k1_xboole_0 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.41  tff(c_825, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_817, c_32])).
% 2.72/1.41  tff(c_902, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_898, c_825])).
% 2.72/1.41  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_902])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 0
% 2.72/1.41  #Sup     : 194
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 5
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 21
% 2.72/1.41  #Demod        : 165
% 2.72/1.41  #Tautology    : 123
% 2.72/1.41  #SimpNegUnit  : 9
% 2.72/1.41  #BackRed      : 2
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 0
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.41  Preprocessing        : 0.32
% 2.72/1.41  Parsing              : 0.17
% 2.72/1.41  CNF conversion       : 0.02
% 2.72/1.41  Main loop            : 0.33
% 2.72/1.41  Inferencing          : 0.13
% 2.72/1.41  Reduction            : 0.10
% 2.72/1.41  Demodulation         : 0.06
% 2.72/1.41  BG Simplification    : 0.02
% 2.72/1.41  Subsumption          : 0.06
% 2.72/1.41  Abstraction          : 0.02
% 2.72/1.41  MUC search           : 0.00
% 2.72/1.41  Cooper               : 0.00
% 2.72/1.42  Total                : 0.69
% 2.72/1.42  Index Insertion      : 0.00
% 2.72/1.42  Index Deletion       : 0.00
% 2.72/1.42  Index Matching       : 0.00
% 2.72/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
