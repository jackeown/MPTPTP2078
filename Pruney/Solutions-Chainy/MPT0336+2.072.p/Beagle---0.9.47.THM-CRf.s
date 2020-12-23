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
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 8.70s
% Output     : CNFRefutation 8.70s
% Verified   : 
% Statistics : Number of formulae       :   75 (  94 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 155 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | r1_xboole_0(A_60,k3_xboole_0(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_412,plain,(
    ! [A_99,B_100,A_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | r1_xboole_0(A_99,k3_xboole_0(A_101,B_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_438,plain,(
    ! [A_101,B_100,A_99] :
      ( r1_xboole_0(k3_xboole_0(A_101,B_100),A_99)
      | ~ r1_xboole_0(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_412,c_4])).

tff(c_121,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_130,plain,(
    ! [A_56,B_57] : r1_tarski(k3_xboole_0(A_56,B_57),A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_18])).

tff(c_612,plain,(
    ! [A_119,B_120,C_121] :
      ( r1_tarski(A_119,B_120)
      | ~ r1_xboole_0(A_119,C_121)
      | ~ r1_tarski(A_119,k2_xboole_0(B_120,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12322,plain,(
    ! [B_469,C_470,B_471] :
      ( r1_tarski(k3_xboole_0(k2_xboole_0(B_469,C_470),B_471),B_469)
      | ~ r1_xboole_0(k3_xboole_0(k2_xboole_0(B_469,C_470),B_471),C_470) ) ),
    inference(resolution,[status(thm)],[c_130,c_612])).

tff(c_13155,plain,(
    ! [B_493,A_494,B_495] :
      ( r1_tarski(k3_xboole_0(k2_xboole_0(B_493,A_494),B_495),B_493)
      | ~ r1_xboole_0(A_494,B_495) ) ),
    inference(resolution,[status(thm)],[c_438,c_12322])).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_257,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,B_83)
      | ~ r2_hidden(C_84,A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_279,plain,(
    ! [C_85] :
      ( ~ r2_hidden(C_85,'#skF_4')
      | ~ r2_hidden(C_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_257])).

tff(c_293,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_279])).

tff(c_106,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_109,plain,(
    ! [B_50,A_49] :
      ( r1_xboole_0(B_50,k1_tarski(A_49))
      | r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_45,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_198,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    ! [A_10,B_11,A_69] :
      ( ~ r1_xboole_0(A_10,B_11)
      | r1_xboole_0(A_69,k3_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_198,c_14])).

tff(c_543,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,k3_xboole_0(B_115,C_116))
      | ~ r1_tarski(A_114,C_116)
      | r1_xboole_0(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_644,plain,(
    ! [A_124,B_125,A_126] :
      ( ~ r1_tarski(A_124,B_125)
      | r1_xboole_0(A_124,A_126)
      | ~ r1_xboole_0(A_126,B_125) ) ),
    inference(resolution,[status(thm)],[c_203,c_543])).

tff(c_657,plain,(
    ! [A_127] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_127)
      | ~ r1_xboole_0(A_127,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_45,c_644])).

tff(c_688,plain,(
    ! [B_50] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_50)
      | r2_hidden('#skF_6',B_50) ) ),
    inference(resolution,[status(thm)],[c_109,c_657])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | r1_xboole_0(A_24,k3_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_155,plain,(
    ! [B_61,C_62,A_60] :
      ( r1_xboole_0(k3_xboole_0(B_61,C_62),A_60)
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_181,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(k3_xboole_0(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_346,plain,(
    ! [B_92,A_93] :
      ( ~ r1_xboole_0(k3_xboole_0(B_92,A_93),B_92)
      | r1_xboole_0(A_93,B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_378,plain,(
    ! [C_94,A_95] :
      ( r1_xboole_0(C_94,A_95)
      | ~ r1_xboole_0(A_95,A_95) ) ),
    inference(resolution,[status(thm)],[c_155,c_346])).

tff(c_1550,plain,(
    ! [C_188,B_189,C_190] :
      ( r1_xboole_0(C_188,k3_xboole_0(B_189,C_190))
      | ~ r1_xboole_0(k3_xboole_0(B_189,C_190),B_189) ) ),
    inference(resolution,[status(thm)],[c_24,c_378])).

tff(c_1577,plain,(
    ! [C_188] :
      ( r1_xboole_0(C_188,k3_xboole_0('#skF_4','#skF_3'))
      | r2_hidden('#skF_6','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_688,c_1550])).

tff(c_1635,plain,(
    ! [C_191] : r1_xboole_0(C_191,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_1577])).

tff(c_28,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,k3_xboole_0(B_30,C_31))
      | ~ r1_tarski(A_29,C_31)
      | r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1810,plain,(
    ! [C_196] :
      ( ~ r1_tarski(C_196,'#skF_3')
      | r1_xboole_0(C_196,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1635,c_28])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( ~ r1_xboole_0(k3_xboole_0(A_27,B_28),B_28)
      | r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1842,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_4')
      | ~ r1_tarski(k3_xboole_0(A_27,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1810,c_26])).

tff(c_13353,plain,(
    ! [A_500] :
      ( r1_xboole_0(k2_xboole_0('#skF_3',A_500),'#skF_4')
      | ~ r1_xboole_0(A_500,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13155,c_1842])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13364,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_13353,c_38])).

tff(c_13372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.70/3.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.29  
% 8.70/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.70/3.29  
% 8.70/3.29  %Foreground sorts:
% 8.70/3.29  
% 8.70/3.29  
% 8.70/3.29  %Background operators:
% 8.70/3.29  
% 8.70/3.29  
% 8.70/3.29  %Foreground operators:
% 8.70/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.70/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.70/3.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.70/3.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.70/3.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.70/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.70/3.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.70/3.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.70/3.29  tff('#skF_5', type, '#skF_5': $i).
% 8.70/3.29  tff('#skF_6', type, '#skF_6': $i).
% 8.70/3.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.70/3.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.70/3.29  tff('#skF_3', type, '#skF_3': $i).
% 8.70/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.70/3.29  tff('#skF_4', type, '#skF_4': $i).
% 8.70/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.70/3.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.70/3.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.70/3.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.70/3.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.70/3.29  
% 8.70/3.31  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.70/3.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.70/3.31  tff(f_81, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 8.70/3.31  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.70/3.31  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.70/3.31  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.70/3.31  tff(f_75, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.70/3.31  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.70/3.31  tff(f_106, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.70/3.31  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.70/3.31  tff(f_95, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 8.70/3.31  tff(f_87, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 8.70/3.31  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.70/3.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.70/3.31  tff(c_146, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | r1_xboole_0(A_60, k3_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.70/3.31  tff(c_412, plain, (![A_99, B_100, A_101]: (~r1_xboole_0(A_99, B_100) | r1_xboole_0(A_99, k3_xboole_0(A_101, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 8.70/3.31  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.70/3.31  tff(c_438, plain, (![A_101, B_100, A_99]: (r1_xboole_0(k3_xboole_0(A_101, B_100), A_99) | ~r1_xboole_0(A_99, B_100))), inference(resolution, [status(thm)], [c_412, c_4])).
% 8.70/3.31  tff(c_121, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.70/3.31  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.70/3.31  tff(c_130, plain, (![A_56, B_57]: (r1_tarski(k3_xboole_0(A_56, B_57), A_56))), inference(superposition, [status(thm), theory('equality')], [c_121, c_18])).
% 8.70/3.31  tff(c_612, plain, (![A_119, B_120, C_121]: (r1_tarski(A_119, B_120) | ~r1_xboole_0(A_119, C_121) | ~r1_tarski(A_119, k2_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.70/3.31  tff(c_12322, plain, (![B_469, C_470, B_471]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_469, C_470), B_471), B_469) | ~r1_xboole_0(k3_xboole_0(k2_xboole_0(B_469, C_470), B_471), C_470))), inference(resolution, [status(thm)], [c_130, c_612])).
% 8.70/3.31  tff(c_13155, plain, (![B_493, A_494, B_495]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_493, A_494), B_495), B_493) | ~r1_xboole_0(A_494, B_495))), inference(resolution, [status(thm)], [c_438, c_12322])).
% 8.70/3.31  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.70/3.31  tff(c_257, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, B_83) | ~r2_hidden(C_84, A_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.70/3.31  tff(c_279, plain, (![C_85]: (~r2_hidden(C_85, '#skF_4') | ~r2_hidden(C_85, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_257])).
% 8.70/3.31  tff(c_293, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_279])).
% 8.70/3.31  tff(c_106, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.70/3.31  tff(c_109, plain, (![B_50, A_49]: (r1_xboole_0(B_50, k1_tarski(A_49)) | r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_106, c_4])).
% 8.70/3.31  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.70/3.31  tff(c_45, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 8.70/3.31  tff(c_198, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), B_70) | r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.70/3.31  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.70/3.31  tff(c_203, plain, (![A_10, B_11, A_69]: (~r1_xboole_0(A_10, B_11) | r1_xboole_0(A_69, k3_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_198, c_14])).
% 8.70/3.31  tff(c_543, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, k3_xboole_0(B_115, C_116)) | ~r1_tarski(A_114, C_116) | r1_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.70/3.31  tff(c_644, plain, (![A_124, B_125, A_126]: (~r1_tarski(A_124, B_125) | r1_xboole_0(A_124, A_126) | ~r1_xboole_0(A_126, B_125))), inference(resolution, [status(thm)], [c_203, c_543])).
% 8.70/3.31  tff(c_657, plain, (![A_127]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_127) | ~r1_xboole_0(A_127, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_45, c_644])).
% 8.70/3.31  tff(c_688, plain, (![B_50]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_50) | r2_hidden('#skF_6', B_50))), inference(resolution, [status(thm)], [c_109, c_657])).
% 8.70/3.31  tff(c_24, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | r1_xboole_0(A_24, k3_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.70/3.31  tff(c_155, plain, (![B_61, C_62, A_60]: (r1_xboole_0(k3_xboole_0(B_61, C_62), A_60) | ~r1_xboole_0(A_60, B_61))), inference(resolution, [status(thm)], [c_146, c_4])).
% 8.70/3.31  tff(c_181, plain, (![A_67, B_68]: (~r1_xboole_0(k3_xboole_0(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.70/3.31  tff(c_346, plain, (![B_92, A_93]: (~r1_xboole_0(k3_xboole_0(B_92, A_93), B_92) | r1_xboole_0(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 8.70/3.31  tff(c_378, plain, (![C_94, A_95]: (r1_xboole_0(C_94, A_95) | ~r1_xboole_0(A_95, A_95))), inference(resolution, [status(thm)], [c_155, c_346])).
% 8.70/3.31  tff(c_1550, plain, (![C_188, B_189, C_190]: (r1_xboole_0(C_188, k3_xboole_0(B_189, C_190)) | ~r1_xboole_0(k3_xboole_0(B_189, C_190), B_189))), inference(resolution, [status(thm)], [c_24, c_378])).
% 8.70/3.31  tff(c_1577, plain, (![C_188]: (r1_xboole_0(C_188, k3_xboole_0('#skF_4', '#skF_3')) | r2_hidden('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_688, c_1550])).
% 8.70/3.31  tff(c_1635, plain, (![C_191]: (r1_xboole_0(C_191, k3_xboole_0('#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_293, c_1577])).
% 8.70/3.31  tff(c_28, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, k3_xboole_0(B_30, C_31)) | ~r1_tarski(A_29, C_31) | r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.70/3.31  tff(c_1810, plain, (![C_196]: (~r1_tarski(C_196, '#skF_3') | r1_xboole_0(C_196, '#skF_4'))), inference(resolution, [status(thm)], [c_1635, c_28])).
% 8.70/3.31  tff(c_26, plain, (![A_27, B_28]: (~r1_xboole_0(k3_xboole_0(A_27, B_28), B_28) | r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.70/3.31  tff(c_1842, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_4') | ~r1_tarski(k3_xboole_0(A_27, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_1810, c_26])).
% 8.70/3.31  tff(c_13353, plain, (![A_500]: (r1_xboole_0(k2_xboole_0('#skF_3', A_500), '#skF_4') | ~r1_xboole_0(A_500, '#skF_4'))), inference(resolution, [status(thm)], [c_13155, c_1842])).
% 8.70/3.31  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.70/3.31  tff(c_13364, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_13353, c_38])).
% 8.70/3.31  tff(c_13372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_13364])).
% 8.70/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/3.31  
% 8.70/3.31  Inference rules
% 8.70/3.31  ----------------------
% 8.70/3.31  #Ref     : 0
% 8.70/3.31  #Sup     : 3071
% 8.70/3.31  #Fact    : 0
% 8.70/3.31  #Define  : 0
% 8.70/3.31  #Split   : 11
% 8.70/3.31  #Chain   : 0
% 8.70/3.31  #Close   : 0
% 8.70/3.31  
% 8.70/3.31  Ordering : KBO
% 8.70/3.31  
% 8.70/3.31  Simplification rules
% 8.70/3.31  ----------------------
% 8.70/3.31  #Subsume      : 887
% 8.70/3.31  #Demod        : 726
% 8.70/3.31  #Tautology    : 739
% 8.70/3.31  #SimpNegUnit  : 2
% 8.70/3.31  #BackRed      : 0
% 8.70/3.31  
% 8.70/3.31  #Partial instantiations: 0
% 8.70/3.31  #Strategies tried      : 1
% 8.70/3.31  
% 8.70/3.31  Timing (in seconds)
% 8.70/3.31  ----------------------
% 8.70/3.31  Preprocessing        : 0.41
% 8.70/3.31  Parsing              : 0.25
% 8.70/3.31  CNF conversion       : 0.02
% 8.70/3.31  Main loop            : 2.04
% 8.70/3.31  Inferencing          : 0.49
% 8.70/3.31  Reduction            : 0.69
% 8.70/3.31  Demodulation         : 0.54
% 8.70/3.31  BG Simplification    : 0.05
% 8.70/3.31  Subsumption          : 0.67
% 8.70/3.31  Abstraction          : 0.06
% 8.70/3.31  MUC search           : 0.00
% 8.70/3.31  Cooper               : 0.00
% 8.70/3.31  Total                : 2.48
% 8.70/3.31  Index Insertion      : 0.00
% 8.70/3.31  Index Deletion       : 0.00
% 8.70/3.31  Index Matching       : 0.00
% 8.70/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
