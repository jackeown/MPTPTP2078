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
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 135 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 213 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_48,plain,(
    ! [C_27] : r2_hidden(C_27,k1_tarski(C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ! [B_37] : ~ r1_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7881,plain,(
    ! [A_395,B_396] :
      ( r2_hidden('#skF_3'(A_395,B_396),k3_xboole_0(A_395,B_396))
      | r1_xboole_0(A_395,B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7968,plain,(
    ! [A_402,B_403] :
      ( r2_hidden('#skF_3'(A_402,B_403),B_403)
      | r1_xboole_0(A_402,B_403) ) ),
    inference(resolution,[status(thm)],[c_7881,c_4])).

tff(c_46,plain,(
    ! [C_27,A_23] :
      ( C_27 = A_23
      | ~ r2_hidden(C_27,k1_tarski(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8088,plain,(
    ! [A_416,A_417] :
      ( '#skF_3'(A_416,k1_tarski(A_417)) = A_417
      | r1_xboole_0(A_416,k1_tarski(A_417)) ) ),
    inference(resolution,[status(thm)],[c_7968,c_46])).

tff(c_8104,plain,(
    ! [A_418] : '#skF_3'(k1_tarski(A_418),k1_tarski(A_418)) = A_418 ),
    inference(resolution,[status(thm)],[c_8088,c_66])).

tff(c_34,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),k3_xboole_0(A_12,B_13))
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8116,plain,(
    ! [A_418] :
      ( r2_hidden(A_418,k3_xboole_0(k1_tarski(A_418),k1_tarski(A_418)))
      | r1_xboole_0(k1_tarski(A_418),k1_tarski(A_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8104,c_34])).

tff(c_8125,plain,(
    ! [A_418] : r2_hidden(A_418,k3_xboole_0(k1_tarski(A_418),k1_tarski(A_418))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_8116])).

tff(c_738,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_3'(A_119,B_120),k3_xboole_0(A_119,B_120))
      | r1_xboole_0(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_769,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_3'(A_121,B_122),B_122)
      | r1_xboole_0(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_738,c_4])).

tff(c_897,plain,(
    ! [A_134,A_135] :
      ( '#skF_3'(A_134,k1_tarski(A_135)) = A_135
      | r1_xboole_0(A_134,k1_tarski(A_135)) ) ),
    inference(resolution,[status(thm)],[c_769,c_46])).

tff(c_910,plain,(
    ! [A_136] : '#skF_3'(k1_tarski(A_136),k1_tarski(A_136)) = A_136 ),
    inference(resolution,[status(thm)],[c_897,c_66])).

tff(c_922,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,k3_xboole_0(k1_tarski(A_136),k1_tarski(A_136)))
      | r1_xboole_0(k1_tarski(A_136),k1_tarski(A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_34])).

tff(c_931,plain,(
    ! [A_136] : r2_hidden(A_136,k3_xboole_0(k1_tarski(A_136),k1_tarski(A_136))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_922])).

tff(c_70,plain,
    ( '#skF_7' != '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_42,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_4'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_183,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(A_67,B_68)
      | k3_xboole_0(A_67,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_243,plain,(
    ! [A_74] : k3_xboole_0(A_74,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_189])).

tff(c_40,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = k4_xboole_0(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_40])).

tff(c_270,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_257])).

tff(c_119,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [B_50,A_49] :
      ( r1_xboole_0(B_50,k1_tarski(A_49))
      | r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_119,c_20])).

tff(c_301,plain,(
    ! [B_77,A_78] :
      ( k3_xboole_0(B_77,k1_tarski(A_78)) = k1_xboole_0
      | r2_hidden(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_126,c_189])).

tff(c_317,plain,(
    ! [B_77,A_78] :
      ( k4_xboole_0(B_77,k1_tarski(A_78)) = k5_xboole_0(B_77,k1_xboole_0)
      | r2_hidden(A_78,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_40])).

tff(c_379,plain,(
    ! [B_81,A_82] :
      ( k4_xboole_0(B_81,k1_tarski(A_82)) = B_81
      | r2_hidden(A_82,B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_317])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_107,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_400,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_107])).

tff(c_406,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_400,c_46])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_406])).

tff(c_411,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_412,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_533,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_412,c_72])).

tff(c_875,plain,(
    ! [A_131,C_132,B_133] :
      ( ~ r2_hidden(A_131,C_132)
      | ~ r2_hidden(A_131,B_133)
      | ~ r2_hidden(A_131,k5_xboole_0(B_133,C_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7005,plain,(
    ! [A_336,A_337,B_338] :
      ( ~ r2_hidden(A_336,k3_xboole_0(A_337,B_338))
      | ~ r2_hidden(A_336,A_337)
      | ~ r2_hidden(A_336,k4_xboole_0(A_337,B_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_875])).

tff(c_7334,plain,(
    ! [A_348] :
      ( ~ r2_hidden(A_348,k3_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')))
      | ~ r2_hidden(A_348,k1_tarski('#skF_9'))
      | ~ r2_hidden(A_348,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_7005])).

tff(c_7434,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_931,c_7334])).

tff(c_7489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7434])).

tff(c_7490,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_7491,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( '#skF_7' != '#skF_8'
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7613,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7490,c_7491,c_74])).

tff(c_8047,plain,(
    ! [A_410,C_411,B_412] :
      ( ~ r2_hidden(A_410,C_411)
      | ~ r2_hidden(A_410,B_412)
      | ~ r2_hidden(A_410,k5_xboole_0(B_412,C_411)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11620,plain,(
    ! [A_559,A_560,B_561] :
      ( ~ r2_hidden(A_559,k3_xboole_0(A_560,B_561))
      | ~ r2_hidden(A_559,A_560)
      | ~ r2_hidden(A_559,k4_xboole_0(A_560,B_561)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8047])).

tff(c_12379,plain,(
    ! [A_574] :
      ( ~ r2_hidden(A_574,k3_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')))
      | ~ r2_hidden(A_574,k1_tarski('#skF_9'))
      | ~ r2_hidden(A_574,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7613,c_11620])).

tff(c_12463,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_8125,c_12379])).

tff(c_12518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.18/2.55  
% 7.18/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.18/2.56  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5
% 7.18/2.56  
% 7.18/2.56  %Foreground sorts:
% 7.18/2.56  
% 7.18/2.56  
% 7.18/2.56  %Background operators:
% 7.18/2.56  
% 7.18/2.56  
% 7.18/2.56  %Foreground operators:
% 7.18/2.56  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.18/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.18/2.56  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.18/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.18/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.18/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.18/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.18/2.56  tff('#skF_7', type, '#skF_7': $i).
% 7.18/2.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.18/2.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.18/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.18/2.56  tff('#skF_10', type, '#skF_10': $i).
% 7.18/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.18/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.18/2.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.18/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.18/2.56  tff('#skF_9', type, '#skF_9': $i).
% 7.18/2.56  tff('#skF_8', type, '#skF_8': $i).
% 7.18/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.18/2.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.18/2.56  
% 7.18/2.57  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.18/2.57  tff(f_96, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 7.18/2.57  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.18/2.57  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.18/2.57  tff(f_102, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 7.18/2.57  tff(f_71, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.18/2.57  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.18/2.57  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.18/2.57  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.18/2.57  tff(f_91, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.18/2.57  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.18/2.57  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.18/2.57  tff(c_48, plain, (![C_27]: (r2_hidden(C_27, k1_tarski(C_27)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.18/2.57  tff(c_66, plain, (![B_37]: (~r1_xboole_0(k1_tarski(B_37), k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.18/2.57  tff(c_7881, plain, (![A_395, B_396]: (r2_hidden('#skF_3'(A_395, B_396), k3_xboole_0(A_395, B_396)) | r1_xboole_0(A_395, B_396))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.18/2.57  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.18/2.57  tff(c_7968, plain, (![A_402, B_403]: (r2_hidden('#skF_3'(A_402, B_403), B_403) | r1_xboole_0(A_402, B_403))), inference(resolution, [status(thm)], [c_7881, c_4])).
% 7.18/2.57  tff(c_46, plain, (![C_27, A_23]: (C_27=A_23 | ~r2_hidden(C_27, k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.18/2.57  tff(c_8088, plain, (![A_416, A_417]: ('#skF_3'(A_416, k1_tarski(A_417))=A_417 | r1_xboole_0(A_416, k1_tarski(A_417)))), inference(resolution, [status(thm)], [c_7968, c_46])).
% 7.18/2.57  tff(c_8104, plain, (![A_418]: ('#skF_3'(k1_tarski(A_418), k1_tarski(A_418))=A_418)), inference(resolution, [status(thm)], [c_8088, c_66])).
% 7.18/2.57  tff(c_34, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), k3_xboole_0(A_12, B_13)) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.18/2.57  tff(c_8116, plain, (![A_418]: (r2_hidden(A_418, k3_xboole_0(k1_tarski(A_418), k1_tarski(A_418))) | r1_xboole_0(k1_tarski(A_418), k1_tarski(A_418)))), inference(superposition, [status(thm), theory('equality')], [c_8104, c_34])).
% 7.18/2.57  tff(c_8125, plain, (![A_418]: (r2_hidden(A_418, k3_xboole_0(k1_tarski(A_418), k1_tarski(A_418))))), inference(negUnitSimplification, [status(thm)], [c_66, c_8116])).
% 7.18/2.57  tff(c_738, plain, (![A_119, B_120]: (r2_hidden('#skF_3'(A_119, B_120), k3_xboole_0(A_119, B_120)) | r1_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.18/2.57  tff(c_769, plain, (![A_121, B_122]: (r2_hidden('#skF_3'(A_121, B_122), B_122) | r1_xboole_0(A_121, B_122))), inference(resolution, [status(thm)], [c_738, c_4])).
% 7.18/2.57  tff(c_897, plain, (![A_134, A_135]: ('#skF_3'(A_134, k1_tarski(A_135))=A_135 | r1_xboole_0(A_134, k1_tarski(A_135)))), inference(resolution, [status(thm)], [c_769, c_46])).
% 7.18/2.57  tff(c_910, plain, (![A_136]: ('#skF_3'(k1_tarski(A_136), k1_tarski(A_136))=A_136)), inference(resolution, [status(thm)], [c_897, c_66])).
% 7.18/2.57  tff(c_922, plain, (![A_136]: (r2_hidden(A_136, k3_xboole_0(k1_tarski(A_136), k1_tarski(A_136))) | r1_xboole_0(k1_tarski(A_136), k1_tarski(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_910, c_34])).
% 7.18/2.57  tff(c_931, plain, (![A_136]: (r2_hidden(A_136, k3_xboole_0(k1_tarski(A_136), k1_tarski(A_136))))), inference(negUnitSimplification, [status(thm)], [c_66, c_922])).
% 7.18/2.57  tff(c_70, plain, ('#skF_7'!='#skF_8' | '#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.18/2.57  tff(c_76, plain, ('#skF_7'!='#skF_8'), inference(splitLeft, [status(thm)], [c_70])).
% 7.18/2.57  tff(c_42, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.18/2.57  tff(c_44, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.18/2.57  tff(c_38, plain, (![A_17]: (r2_hidden('#skF_4'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.18/2.57  tff(c_183, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.18/2.57  tff(c_189, plain, (![A_67, B_68]: (~r1_xboole_0(A_67, B_68) | k3_xboole_0(A_67, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_183])).
% 7.18/2.57  tff(c_243, plain, (![A_74]: (k3_xboole_0(A_74, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_189])).
% 7.18/2.57  tff(c_40, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.18/2.57  tff(c_257, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=k4_xboole_0(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_243, c_40])).
% 7.18/2.57  tff(c_270, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_257])).
% 7.18/2.57  tff(c_119, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.18/2.57  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.57  tff(c_126, plain, (![B_50, A_49]: (r1_xboole_0(B_50, k1_tarski(A_49)) | r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_119, c_20])).
% 7.18/2.57  tff(c_301, plain, (![B_77, A_78]: (k3_xboole_0(B_77, k1_tarski(A_78))=k1_xboole_0 | r2_hidden(A_78, B_77))), inference(resolution, [status(thm)], [c_126, c_189])).
% 7.18/2.57  tff(c_317, plain, (![B_77, A_78]: (k4_xboole_0(B_77, k1_tarski(A_78))=k5_xboole_0(B_77, k1_xboole_0) | r2_hidden(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_301, c_40])).
% 7.18/2.57  tff(c_379, plain, (![B_81, A_82]: (k4_xboole_0(B_81, k1_tarski(A_82))=B_81 | r2_hidden(A_82, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_317])).
% 7.18/2.57  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | '#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.18/2.57  tff(c_107, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_68])).
% 7.18/2.57  tff(c_400, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_379, c_107])).
% 7.18/2.57  tff(c_406, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_400, c_46])).
% 7.18/2.57  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_406])).
% 7.18/2.57  tff(c_411, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_68])).
% 7.18/2.57  tff(c_412, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 7.18/2.57  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.18/2.57  tff(c_533, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_412, c_72])).
% 7.18/2.57  tff(c_875, plain, (![A_131, C_132, B_133]: (~r2_hidden(A_131, C_132) | ~r2_hidden(A_131, B_133) | ~r2_hidden(A_131, k5_xboole_0(B_133, C_132)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.57  tff(c_7005, plain, (![A_336, A_337, B_338]: (~r2_hidden(A_336, k3_xboole_0(A_337, B_338)) | ~r2_hidden(A_336, A_337) | ~r2_hidden(A_336, k4_xboole_0(A_337, B_338)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_875])).
% 7.18/2.57  tff(c_7334, plain, (![A_348]: (~r2_hidden(A_348, k3_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))) | ~r2_hidden(A_348, k1_tarski('#skF_9')) | ~r2_hidden(A_348, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_533, c_7005])).
% 7.18/2.57  tff(c_7434, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_931, c_7334])).
% 7.18/2.57  tff(c_7489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_7434])).
% 7.18/2.57  tff(c_7490, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_70])).
% 7.18/2.57  tff(c_7491, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 7.18/2.57  tff(c_74, plain, ('#skF_7'!='#skF_8' | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.18/2.57  tff(c_7613, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7490, c_7491, c_74])).
% 7.18/2.57  tff(c_8047, plain, (![A_410, C_411, B_412]: (~r2_hidden(A_410, C_411) | ~r2_hidden(A_410, B_412) | ~r2_hidden(A_410, k5_xboole_0(B_412, C_411)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.18/2.57  tff(c_11620, plain, (![A_559, A_560, B_561]: (~r2_hidden(A_559, k3_xboole_0(A_560, B_561)) | ~r2_hidden(A_559, A_560) | ~r2_hidden(A_559, k4_xboole_0(A_560, B_561)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_8047])).
% 7.18/2.57  tff(c_12379, plain, (![A_574]: (~r2_hidden(A_574, k3_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))) | ~r2_hidden(A_574, k1_tarski('#skF_9')) | ~r2_hidden(A_574, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_7613, c_11620])).
% 7.18/2.57  tff(c_12463, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_8125, c_12379])).
% 7.18/2.57  tff(c_12518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_12463])).
% 7.18/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.18/2.57  
% 7.18/2.57  Inference rules
% 7.18/2.57  ----------------------
% 7.18/2.57  #Ref     : 0
% 7.18/2.57  #Sup     : 2919
% 7.18/2.57  #Fact    : 0
% 7.18/2.57  #Define  : 0
% 7.18/2.57  #Split   : 2
% 7.18/2.57  #Chain   : 0
% 7.18/2.57  #Close   : 0
% 7.18/2.57  
% 7.18/2.57  Ordering : KBO
% 7.18/2.57  
% 7.18/2.57  Simplification rules
% 7.18/2.57  ----------------------
% 7.18/2.57  #Subsume      : 697
% 7.18/2.57  #Demod        : 1195
% 7.18/2.57  #Tautology    : 1371
% 7.18/2.57  #SimpNegUnit  : 195
% 7.18/2.57  #BackRed      : 0
% 7.18/2.57  
% 7.18/2.57  #Partial instantiations: 0
% 7.18/2.57  #Strategies tried      : 1
% 7.18/2.57  
% 7.18/2.57  Timing (in seconds)
% 7.18/2.57  ----------------------
% 7.18/2.58  Preprocessing        : 0.33
% 7.18/2.58  Parsing              : 0.17
% 7.18/2.58  CNF conversion       : 0.03
% 7.18/2.58  Main loop            : 1.49
% 7.18/2.58  Inferencing          : 0.54
% 7.18/2.58  Reduction            : 0.43
% 7.18/2.58  Demodulation         : 0.29
% 7.18/2.58  BG Simplification    : 0.06
% 7.18/2.58  Subsumption          : 0.35
% 7.18/2.58  Abstraction          : 0.08
% 7.18/2.58  MUC search           : 0.00
% 7.18/2.58  Cooper               : 0.00
% 7.18/2.58  Total                : 1.85
% 7.18/2.58  Index Insertion      : 0.00
% 7.18/2.58  Index Deletion       : 0.00
% 7.18/2.58  Index Matching       : 0.00
% 7.18/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
