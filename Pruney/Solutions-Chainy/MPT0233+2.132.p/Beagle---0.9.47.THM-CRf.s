%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 521 expanded)
%              Number of leaves         :   29 ( 175 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 (1095 expanded)
%              Number of equality atoms :   99 ( 582 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_48,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_67,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_359,plain,(
    ! [B_90,A_91,C_92] :
      ( r1_xboole_0(B_90,k4_xboole_0(A_91,C_92))
      | ~ r1_xboole_0(A_91,k4_xboole_0(B_90,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_496,plain,(
    ! [B_103,A_104] :
      ( r1_xboole_0(B_103,k4_xboole_0(A_104,B_103))
      | ~ r1_xboole_0(A_104,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_359])).

tff(c_139,plain,(
    ! [A_59,B_60] : k2_xboole_0(k3_xboole_0(A_59,B_60),k4_xboole_0(A_59,B_60)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [B_61] : k2_xboole_0(k3_xboole_0(B_61,B_61),k1_xboole_0) = B_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_139])).

tff(c_20,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_176,plain,(
    ! [A_8,B_61] :
      ( r1_xboole_0(A_8,k1_xboole_0)
      | ~ r1_xboole_0(A_8,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_20])).

tff(c_521,plain,(
    ! [B_103,A_104] :
      ( r1_xboole_0(B_103,k1_xboole_0)
      | ~ r1_xboole_0(A_104,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_496,c_176])).

tff(c_533,plain,(
    ! [A_104] : ~ r1_xboole_0(A_104,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [B_20,C_21] : r1_tarski(k1_xboole_0,k2_tarski(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_86,plain,(
    ! [B_20,C_21] : k4_xboole_0(k1_xboole_0,k2_tarski(B_20,C_21)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_514,plain,(
    ! [B_20,C_21] :
      ( r1_xboole_0(k2_tarski(B_20,C_21),k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_496])).

tff(c_523,plain,(
    ! [B_20,C_21] : r1_xboole_0(k2_tarski(B_20,C_21),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_514])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_523])).

tff(c_548,plain,(
    ! [B_107] : r1_xboole_0(B_107,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_216,plain,(
    ! [A_69,A_70,B_71] :
      ( r1_xboole_0(A_69,k4_xboole_0(A_70,B_71))
      | ~ r1_xboole_0(A_69,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_20])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_239,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(A_70,B_71),A_70) ) ),
    inference(resolution,[status(thm)],[c_216,c_16])).

tff(c_561,plain,(
    ! [B_71] : k4_xboole_0(k1_xboole_0,B_71) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_548,c_239])).

tff(c_52,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_710,plain,(
    ! [B_117,C_118,A_119] :
      ( k2_tarski(B_117,C_118) = A_119
      | k1_tarski(C_118) = A_119
      | k1_tarski(B_117) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k2_tarski(B_117,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_732,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_710])).

tff(c_745,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_34,plain,(
    ! [C_21,B_20] : r1_tarski(k1_tarski(C_21),k2_tarski(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_773,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_34])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_187,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_187])).

tff(c_788,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_773,c_200])).

tff(c_796,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_788])).

tff(c_12,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_xboole_0(A_66,B_67)
      | ~ r1_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_241,plain,(
    ! [A_74,A_75,B_76] :
      ( r1_xboole_0(A_74,k3_xboole_0(A_75,B_76))
      | ~ r1_xboole_0(A_74,A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_209])).

tff(c_249,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_xboole_0(k3_xboole_0(A_75,B_76),A_75) ) ),
    inference(resolution,[status(thm)],[c_241,c_16])).

tff(c_562,plain,(
    ! [B_76] : k3_xboole_0(k1_xboole_0,B_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_548,c_249])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( B_25 = A_24
      | k3_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) != k1_tarski(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_807,plain,(
    ! [B_25] :
      ( B_25 = '#skF_2'
      | k3_xboole_0(k1_xboole_0,k1_tarski(B_25)) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_42])).

tff(c_835,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_562,c_807])).

tff(c_828,plain,(
    ! [B_25] : B_25 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_562,c_807])).

tff(c_977,plain,(
    ! [B_951] : B_951 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_828])).

tff(c_1103,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_50])).

tff(c_1104,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_1406,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_201,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_187])).

tff(c_263,plain,(
    ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_267,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_263])).

tff(c_1409,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_267])).

tff(c_1417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1409])).

tff(c_1418,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_1420,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1418])).

tff(c_46,plain,(
    ! [C_31,B_30,A_29] :
      ( C_31 = B_30
      | k2_tarski(B_30,C_31) != k1_tarski(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1472,plain,(
    ! [A_29] :
      ( '#skF_2' = '#skF_1'
      | k1_tarski(A_29) != k1_tarski('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_46])).

tff(c_1534,plain,(
    ! [A_29] : k1_tarski(A_29) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_1538,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1534])).

tff(c_1539,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_44,plain,(
    ! [C_28,A_26,B_27] :
      ( C_28 = A_26
      | B_27 = A_26
      | ~ r1_tarski(k1_tarski(A_26),k2_tarski(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1460,plain,(
    ! [A_26] :
      ( A_26 = '#skF_2'
      | A_26 = '#skF_1'
      | ~ r1_tarski(k1_tarski(A_26),k1_tarski('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_44])).

tff(c_1854,plain,(
    ! [A_1832] :
      ( A_1832 = '#skF_1'
      | A_1832 = '#skF_1'
      | ~ r1_tarski(k1_tarski(A_1832),k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1539,c_1460])).

tff(c_1864,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_1854])).

tff(c_1871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_1864])).

tff(c_1872,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1418])).

tff(c_1926,plain,(
    ! [A_29] :
      ( '#skF_2' = '#skF_1'
      | k1_tarski(A_29) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_46])).

tff(c_1988,plain,(
    ! [A_29] : k1_tarski(A_29) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1926])).

tff(c_1992,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1988])).

tff(c_1993,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1926])).

tff(c_1914,plain,(
    ! [A_26] :
      ( A_26 = '#skF_2'
      | A_26 = '#skF_1'
      | ~ r1_tarski(k1_tarski(A_26),k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_44])).

tff(c_2308,plain,(
    ! [A_1850] :
      ( A_1850 = '#skF_1'
      | A_1850 = '#skF_1'
      | ~ r1_tarski(k1_tarski(A_1850),k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1993,c_1914])).

tff(c_2318,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_2308])).

tff(c_2325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_2318])).

tff(c_2326,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_2348,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_34])).

tff(c_2385,plain,(
    ! [C_1851,A_1852,B_1853] :
      ( C_1851 = A_1852
      | B_1853 = A_1852
      | ~ r1_tarski(k1_tarski(A_1852),k2_tarski(B_1853,C_1851)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2391,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2348,c_2385])).

tff(c_2409,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2391])).

tff(c_40,plain,(
    ! [A_22,B_23] : r1_tarski(k1_tarski(A_22),k2_tarski(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2351,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_40])).

tff(c_2388,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2351,c_2385])).

tff(c_2406,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2388])).

tff(c_2424,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2409,c_2406])).

tff(c_2418,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2326])).

tff(c_2445,plain,(
    k2_tarski('#skF_1','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_2424,c_2418])).

tff(c_2470,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_4','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2445,c_40])).

tff(c_2486,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2470,c_44])).

tff(c_2495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_2486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:43:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  %$ r1_xboole_0 > r1_tarski > k5_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.95/1.70  
% 3.95/1.70  %Foreground sorts:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Background operators:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Foreground operators:
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.95/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.95/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.95/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.95/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.95/1.70  
% 3.95/1.72  tff(f_117, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.95/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.72  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.95/1.72  tff(f_69, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 3.95/1.72  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.95/1.72  tff(f_65, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.95/1.72  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.95/1.72  tff(f_88, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.95/1.72  tff(f_94, axiom, (![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.95/1.72  tff(f_107, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 3.95/1.72  tff(f_103, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.95/1.72  tff(f_90, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.95/1.72  tff(c_48, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.95/1.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.72  tff(c_50, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.95/1.72  tff(c_67, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.72  tff(c_87, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_67])).
% 3.95/1.72  tff(c_359, plain, (![B_90, A_91, C_92]: (r1_xboole_0(B_90, k4_xboole_0(A_91, C_92)) | ~r1_xboole_0(A_91, k4_xboole_0(B_90, C_92)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.95/1.72  tff(c_496, plain, (![B_103, A_104]: (r1_xboole_0(B_103, k4_xboole_0(A_104, B_103)) | ~r1_xboole_0(A_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_87, c_359])).
% 3.95/1.72  tff(c_139, plain, (![A_59, B_60]: (k2_xboole_0(k3_xboole_0(A_59, B_60), k4_xboole_0(A_59, B_60))=A_59)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.95/1.72  tff(c_170, plain, (![B_61]: (k2_xboole_0(k3_xboole_0(B_61, B_61), k1_xboole_0)=B_61)), inference(superposition, [status(thm), theory('equality')], [c_87, c_139])).
% 3.95/1.72  tff(c_20, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.72  tff(c_176, plain, (![A_8, B_61]: (r1_xboole_0(A_8, k1_xboole_0) | ~r1_xboole_0(A_8, B_61))), inference(superposition, [status(thm), theory('equality')], [c_170, c_20])).
% 3.95/1.72  tff(c_521, plain, (![B_103, A_104]: (r1_xboole_0(B_103, k1_xboole_0) | ~r1_xboole_0(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_496, c_176])).
% 3.95/1.72  tff(c_533, plain, (![A_104]: (~r1_xboole_0(A_104, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_521])).
% 3.95/1.72  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.72  tff(c_38, plain, (![B_20, C_21]: (r1_tarski(k1_xboole_0, k2_tarski(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.95/1.72  tff(c_86, plain, (![B_20, C_21]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_20, C_21))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_67])).
% 3.95/1.72  tff(c_514, plain, (![B_20, C_21]: (r1_xboole_0(k2_tarski(B_20, C_21), k1_xboole_0) | ~r1_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86, c_496])).
% 3.95/1.72  tff(c_523, plain, (![B_20, C_21]: (r1_xboole_0(k2_tarski(B_20, C_21), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_514])).
% 3.95/1.72  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_523])).
% 3.95/1.72  tff(c_548, plain, (![B_107]: (r1_xboole_0(B_107, k1_xboole_0))), inference(splitRight, [status(thm)], [c_521])).
% 3.95/1.72  tff(c_216, plain, (![A_69, A_70, B_71]: (r1_xboole_0(A_69, k4_xboole_0(A_70, B_71)) | ~r1_xboole_0(A_69, A_70))), inference(superposition, [status(thm), theory('equality')], [c_139, c_20])).
% 3.95/1.72  tff(c_16, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.72  tff(c_239, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(A_70, B_71), A_70))), inference(resolution, [status(thm)], [c_216, c_16])).
% 3.95/1.72  tff(c_561, plain, (![B_71]: (k4_xboole_0(k1_xboole_0, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_548, c_239])).
% 3.95/1.72  tff(c_52, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.95/1.72  tff(c_710, plain, (![B_117, C_118, A_119]: (k2_tarski(B_117, C_118)=A_119 | k1_tarski(C_118)=A_119 | k1_tarski(B_117)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k2_tarski(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.95/1.72  tff(c_732, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_710])).
% 3.95/1.72  tff(c_745, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_732])).
% 3.95/1.72  tff(c_34, plain, (![C_21, B_20]: (r1_tarski(k1_tarski(C_21), k2_tarski(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.95/1.72  tff(c_773, plain, (r1_tarski(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_745, c_34])).
% 3.95/1.72  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.72  tff(c_187, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.72  tff(c_200, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_187])).
% 3.95/1.72  tff(c_788, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_773, c_200])).
% 3.95/1.72  tff(c_796, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_561, c_788])).
% 3.95/1.72  tff(c_12, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.95/1.72  tff(c_209, plain, (![A_66, B_67, C_68]: (r1_xboole_0(A_66, B_67) | ~r1_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.72  tff(c_241, plain, (![A_74, A_75, B_76]: (r1_xboole_0(A_74, k3_xboole_0(A_75, B_76)) | ~r1_xboole_0(A_74, A_75))), inference(superposition, [status(thm), theory('equality')], [c_12, c_209])).
% 3.95/1.72  tff(c_249, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_xboole_0(k3_xboole_0(A_75, B_76), A_75))), inference(resolution, [status(thm)], [c_241, c_16])).
% 3.95/1.72  tff(c_562, plain, (![B_76]: (k3_xboole_0(k1_xboole_0, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_548, c_249])).
% 3.95/1.72  tff(c_42, plain, (![B_25, A_24]: (B_25=A_24 | k3_xboole_0(k1_tarski(A_24), k1_tarski(B_25))!=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.95/1.72  tff(c_807, plain, (![B_25]: (B_25='#skF_2' | k3_xboole_0(k1_xboole_0, k1_tarski(B_25))!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_42])).
% 3.95/1.72  tff(c_835, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_796, c_562, c_807])).
% 3.95/1.72  tff(c_828, plain, (![B_25]: (B_25='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_562, c_807])).
% 3.95/1.72  tff(c_977, plain, (![B_951]: (B_951='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_835, c_828])).
% 3.95/1.72  tff(c_1103, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_977, c_50])).
% 3.95/1.72  tff(c_1104, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_732])).
% 3.95/1.72  tff(c_1406, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_1104])).
% 3.95/1.72  tff(c_201, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | ~r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_187])).
% 3.95/1.72  tff(c_263, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_201])).
% 3.95/1.72  tff(c_267, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_263])).
% 3.95/1.72  tff(c_1409, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_267])).
% 3.95/1.72  tff(c_1417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1409])).
% 3.95/1.72  tff(c_1418, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_1104])).
% 3.95/1.72  tff(c_1420, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_1418])).
% 3.95/1.72  tff(c_46, plain, (![C_31, B_30, A_29]: (C_31=B_30 | k2_tarski(B_30, C_31)!=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.95/1.72  tff(c_1472, plain, (![A_29]: ('#skF_2'='#skF_1' | k1_tarski(A_29)!=k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_46])).
% 3.95/1.72  tff(c_1534, plain, (![A_29]: (k1_tarski(A_29)!=k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_1472])).
% 3.95/1.72  tff(c_1538, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1534])).
% 3.95/1.72  tff(c_1539, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1472])).
% 3.95/1.72  tff(c_44, plain, (![C_28, A_26, B_27]: (C_28=A_26 | B_27=A_26 | ~r1_tarski(k1_tarski(A_26), k2_tarski(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.72  tff(c_1460, plain, (![A_26]: (A_26='#skF_2' | A_26='#skF_1' | ~r1_tarski(k1_tarski(A_26), k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_44])).
% 3.95/1.72  tff(c_1854, plain, (![A_1832]: (A_1832='#skF_1' | A_1832='#skF_1' | ~r1_tarski(k1_tarski(A_1832), k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1539, c_1460])).
% 3.95/1.72  tff(c_1864, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_6, c_1854])).
% 3.95/1.72  tff(c_1871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_1864])).
% 3.95/1.72  tff(c_1872, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_1418])).
% 3.95/1.72  tff(c_1926, plain, (![A_29]: ('#skF_2'='#skF_1' | k1_tarski(A_29)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1872, c_46])).
% 3.95/1.72  tff(c_1988, plain, (![A_29]: (k1_tarski(A_29)!=k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_1926])).
% 3.95/1.72  tff(c_1992, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1988])).
% 3.95/1.72  tff(c_1993, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1926])).
% 3.95/1.72  tff(c_1914, plain, (![A_26]: (A_26='#skF_2' | A_26='#skF_1' | ~r1_tarski(k1_tarski(A_26), k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1872, c_44])).
% 3.95/1.72  tff(c_2308, plain, (![A_1850]: (A_1850='#skF_1' | A_1850='#skF_1' | ~r1_tarski(k1_tarski(A_1850), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1993, c_1914])).
% 3.95/1.72  tff(c_2318, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_6, c_2308])).
% 3.95/1.72  tff(c_2325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_2318])).
% 3.95/1.72  tff(c_2326, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_201])).
% 3.95/1.72  tff(c_2348, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2326, c_34])).
% 3.95/1.72  tff(c_2385, plain, (![C_1851, A_1852, B_1853]: (C_1851=A_1852 | B_1853=A_1852 | ~r1_tarski(k1_tarski(A_1852), k2_tarski(B_1853, C_1851)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.72  tff(c_2391, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2348, c_2385])).
% 3.95/1.72  tff(c_2409, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_2391])).
% 3.95/1.72  tff(c_40, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), k2_tarski(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.95/1.72  tff(c_2351, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2326, c_40])).
% 3.95/1.72  tff(c_2388, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2351, c_2385])).
% 3.95/1.72  tff(c_2406, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_2388])).
% 3.95/1.72  tff(c_2424, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2409, c_2406])).
% 3.95/1.72  tff(c_2418, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2326])).
% 3.95/1.72  tff(c_2445, plain, (k2_tarski('#skF_1', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2424, c_2424, c_2418])).
% 3.95/1.72  tff(c_2470, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2445, c_40])).
% 3.95/1.72  tff(c_2486, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2470, c_44])).
% 3.95/1.72  tff(c_2495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_2486])).
% 3.95/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.72  
% 3.95/1.72  Inference rules
% 3.95/1.72  ----------------------
% 3.95/1.72  #Ref     : 2
% 3.95/1.72  #Sup     : 632
% 3.95/1.72  #Fact    : 0
% 3.95/1.72  #Define  : 0
% 3.95/1.72  #Split   : 8
% 3.95/1.72  #Chain   : 0
% 3.95/1.72  #Close   : 0
% 3.95/1.72  
% 3.95/1.72  Ordering : KBO
% 3.95/1.72  
% 3.95/1.72  Simplification rules
% 3.95/1.72  ----------------------
% 3.95/1.72  #Subsume      : 69
% 3.95/1.72  #Demod        : 371
% 3.95/1.72  #Tautology    : 297
% 3.95/1.72  #SimpNegUnit  : 18
% 3.95/1.72  #BackRed      : 47
% 3.95/1.72  
% 3.95/1.72  #Partial instantiations: 172
% 3.95/1.72  #Strategies tried      : 1
% 3.95/1.72  
% 3.95/1.72  Timing (in seconds)
% 3.95/1.72  ----------------------
% 3.95/1.72  Preprocessing        : 0.31
% 3.95/1.72  Parsing              : 0.16
% 3.95/1.72  CNF conversion       : 0.02
% 3.95/1.72  Main loop            : 0.63
% 3.95/1.72  Inferencing          : 0.23
% 3.95/1.72  Reduction            : 0.21
% 3.95/1.72  Demodulation         : 0.15
% 3.95/1.72  BG Simplification    : 0.03
% 3.95/1.72  Subsumption          : 0.12
% 3.95/1.72  Abstraction          : 0.03
% 3.95/1.72  MUC search           : 0.00
% 3.95/1.72  Cooper               : 0.00
% 3.95/1.72  Total                : 0.98
% 3.95/1.72  Index Insertion      : 0.00
% 3.95/1.72  Index Deletion       : 0.00
% 3.95/1.72  Index Matching       : 0.00
% 3.95/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
