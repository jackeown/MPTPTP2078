%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 231 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 406 expanded)
%              Number of equality atoms :   62 ( 215 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_tarski(A_16),B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_100,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_42,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_216,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_216,c_4])).

tff(c_224,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_218])).

tff(c_233,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_224])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_165,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(k1_tarski(A_42),B_43)
      | r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_187,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,k1_tarski(A_47))
      | r2_hidden(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_319,plain,(
    ! [B_63,A_64] :
      ( k4_xboole_0(B_63,k1_tarski(A_64)) = B_63
      | r2_hidden(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_187,c_16])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_216,c_12])).

tff(c_335,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_225])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_64,c_335])).

tff(c_369,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_375,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_173,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_155,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_184,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_155])).

tff(c_376,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_184])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_376])).

tff(c_381,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_14,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,A_24)
      | ~ r1_xboole_0(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_7] : r1_xboole_0(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_14,c_55])).

tff(c_65,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_387,plain,(
    ! [A_7] : k4_xboole_0('#skF_1',A_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_381,c_72])).

tff(c_383,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_184])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_383])).

tff(c_480,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_541,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_547,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_480,c_541])).

tff(c_556,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_547])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_556])).

tff(c_508,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(k1_tarski(A_74),B_75)
      | r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_533,plain,(
    ! [B_80,A_81] :
      ( r1_xboole_0(B_80,k1_tarski(A_81))
      | r2_hidden(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_508,c_2])).

tff(c_695,plain,(
    ! [B_95,A_96] :
      ( k4_xboole_0(B_95,k1_tarski(A_96)) = B_95
      | r2_hidden(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_533,c_16])).

tff(c_485,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_480,c_12])).

tff(c_716,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_485])).

tff(c_754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_569,c_64,c_716])).

tff(c_756,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_757,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_757])).

tff(c_770,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_783,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_755,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_784,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_755])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_784])).

tff(c_788,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_802,plain,(
    ! [A_97] : r1_xboole_0(A_97,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_14])).

tff(c_810,plain,(
    ! [A_98] : r1_xboole_0('#skF_1',A_98) ),
    inference(resolution,[status(thm)],[c_802,c_2])).

tff(c_816,plain,(
    ! [A_98] : k4_xboole_0('#skF_1',A_98) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_810,c_16])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_951,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(A_116,B_117)
      | k4_xboole_0(A_116,B_117) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_10])).

tff(c_954,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_951,c_755])).

tff(c_962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_954])).

tff(c_964,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1008,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_964,c_38])).

tff(c_1009,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_965,plain,(
    ! [A_7] : r1_xboole_0('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_58])).

tff(c_1012,plain,(
    ! [A_7] : r1_xboole_0('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_965])).

tff(c_1057,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(A_137,B_138) = A_137
      | ~ r1_xboole_0(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1071,plain,(
    ! [A_7] : k4_xboole_0('#skF_1',A_7) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1012,c_1057])).

tff(c_1014,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_964])).

tff(c_1075,plain,(
    ! [A_139,B_140] :
      ( r1_tarski(A_139,B_140)
      | k4_xboole_0(A_139,B_140) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_10])).

tff(c_963,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1084,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1075,c_963])).

tff(c_1130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1084])).

tff(c_1131,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_1135,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_963])).

tff(c_1138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:17:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.43  
% 2.68/1.43  %Foreground sorts:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Background operators:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Foreground operators:
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.43  
% 2.68/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.45  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.68/1.45  tff(f_67, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.68/1.45  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.68/1.45  tff(f_60, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.68/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.68/1.45  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.68/1.45  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.68/1.45  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.45  tff(c_28, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.45  tff(c_32, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.45  tff(c_137, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 2.68/1.45  tff(c_100, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.45  tff(c_104, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_100])).
% 2.68/1.45  tff(c_42, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.45  tff(c_216, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.68/1.45  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.45  tff(c_218, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_216, c_4])).
% 2.68/1.45  tff(c_224, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_137, c_218])).
% 2.68/1.45  tff(c_233, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_224])).
% 2.68/1.45  tff(c_36, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.45  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 2.68/1.45  tff(c_165, plain, (![A_42, B_43]: (r1_xboole_0(k1_tarski(A_42), B_43) | r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.45  tff(c_187, plain, (![B_46, A_47]: (r1_xboole_0(B_46, k1_tarski(A_47)) | r2_hidden(A_47, B_46))), inference(resolution, [status(thm)], [c_165, c_2])).
% 2.68/1.45  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.45  tff(c_319, plain, (![B_63, A_64]: (k4_xboole_0(B_63, k1_tarski(A_64))=B_63 | r2_hidden(A_64, B_63))), inference(resolution, [status(thm)], [c_187, c_16])).
% 2.68/1.45  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.45  tff(c_225, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_216, c_12])).
% 2.68/1.45  tff(c_335, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_319, c_225])).
% 2.68/1.45  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_64, c_335])).
% 2.68/1.45  tff(c_369, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 2.68/1.45  tff(c_375, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_369])).
% 2.68/1.45  tff(c_173, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.45  tff(c_40, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.45  tff(c_155, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.68/1.45  tff(c_184, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_173, c_155])).
% 2.68/1.45  tff(c_376, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_375, c_184])).
% 2.68/1.45  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_376])).
% 2.68/1.45  tff(c_381, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_369])).
% 2.68/1.45  tff(c_14, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.45  tff(c_55, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.45  tff(c_58, plain, (![A_7]: (r1_xboole_0(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_14, c_55])).
% 2.68/1.45  tff(c_65, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.45  tff(c_72, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_65])).
% 2.68/1.45  tff(c_387, plain, (![A_7]: (k4_xboole_0('#skF_1', A_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_381, c_72])).
% 2.68/1.45  tff(c_383, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_381, c_184])).
% 2.68/1.45  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_383])).
% 2.68/1.45  tff(c_480, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 2.68/1.45  tff(c_541, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.45  tff(c_547, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_480, c_541])).
% 2.68/1.45  tff(c_556, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_137, c_547])).
% 2.68/1.45  tff(c_569, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_556])).
% 2.68/1.45  tff(c_508, plain, (![A_74, B_75]: (r1_xboole_0(k1_tarski(A_74), B_75) | r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.45  tff(c_533, plain, (![B_80, A_81]: (r1_xboole_0(B_80, k1_tarski(A_81)) | r2_hidden(A_81, B_80))), inference(resolution, [status(thm)], [c_508, c_2])).
% 2.68/1.45  tff(c_695, plain, (![B_95, A_96]: (k4_xboole_0(B_95, k1_tarski(A_96))=B_95 | r2_hidden(A_96, B_95))), inference(resolution, [status(thm)], [c_533, c_16])).
% 2.68/1.45  tff(c_485, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_480, c_12])).
% 2.68/1.45  tff(c_716, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_695, c_485])).
% 2.68/1.45  tff(c_754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_569, c_64, c_716])).
% 2.68/1.45  tff(c_756, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.68/1.45  tff(c_34, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.45  tff(c_757, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.68/1.45  tff(c_769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_756, c_757])).
% 2.68/1.45  tff(c_770, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.68/1.45  tff(c_783, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_770])).
% 2.68/1.45  tff(c_755, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.68/1.45  tff(c_784, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_755])).
% 2.68/1.45  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_784])).
% 2.68/1.45  tff(c_788, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_770])).
% 2.68/1.45  tff(c_802, plain, (![A_97]: (r1_xboole_0(A_97, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_788, c_14])).
% 2.68/1.45  tff(c_810, plain, (![A_98]: (r1_xboole_0('#skF_1', A_98))), inference(resolution, [status(thm)], [c_802, c_2])).
% 2.68/1.45  tff(c_816, plain, (![A_98]: (k4_xboole_0('#skF_1', A_98)='#skF_1')), inference(resolution, [status(thm)], [c_810, c_16])).
% 2.68/1.45  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.45  tff(c_951, plain, (![A_116, B_117]: (r1_tarski(A_116, B_117) | k4_xboole_0(A_116, B_117)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_10])).
% 2.68/1.45  tff(c_954, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_951, c_755])).
% 2.68/1.45  tff(c_962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_816, c_954])).
% 2.68/1.45  tff(c_964, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.68/1.45  tff(c_38, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.45  tff(c_1008, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_964, c_964, c_38])).
% 2.68/1.45  tff(c_1009, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_1008])).
% 2.68/1.45  tff(c_965, plain, (![A_7]: (r1_xboole_0('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_964, c_58])).
% 2.68/1.45  tff(c_1012, plain, (![A_7]: (r1_xboole_0('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_965])).
% 2.68/1.45  tff(c_1057, plain, (![A_137, B_138]: (k4_xboole_0(A_137, B_138)=A_137 | ~r1_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.45  tff(c_1071, plain, (![A_7]: (k4_xboole_0('#skF_1', A_7)='#skF_1')), inference(resolution, [status(thm)], [c_1012, c_1057])).
% 2.68/1.45  tff(c_1014, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_964])).
% 2.68/1.45  tff(c_1075, plain, (![A_139, B_140]: (r1_tarski(A_139, B_140) | k4_xboole_0(A_139, B_140)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_10])).
% 2.68/1.45  tff(c_963, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 2.68/1.45  tff(c_1084, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_1075, c_963])).
% 2.68/1.45  tff(c_1130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1084])).
% 2.68/1.45  tff(c_1131, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1008])).
% 2.68/1.45  tff(c_1135, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_963])).
% 2.68/1.45  tff(c_1138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1135])).
% 2.68/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.45  
% 2.68/1.45  Inference rules
% 2.68/1.45  ----------------------
% 2.68/1.45  #Ref     : 0
% 2.68/1.45  #Sup     : 243
% 2.68/1.45  #Fact    : 0
% 2.68/1.45  #Define  : 0
% 2.68/1.45  #Split   : 10
% 2.68/1.45  #Chain   : 0
% 2.68/1.45  #Close   : 0
% 2.68/1.45  
% 2.68/1.45  Ordering : KBO
% 2.68/1.45  
% 2.68/1.45  Simplification rules
% 2.68/1.45  ----------------------
% 2.68/1.45  #Subsume      : 16
% 2.68/1.45  #Demod        : 83
% 2.68/1.45  #Tautology    : 144
% 2.68/1.45  #SimpNegUnit  : 8
% 2.68/1.45  #BackRed      : 27
% 2.68/1.45  
% 2.68/1.45  #Partial instantiations: 0
% 2.68/1.45  #Strategies tried      : 1
% 2.68/1.45  
% 2.68/1.45  Timing (in seconds)
% 2.68/1.45  ----------------------
% 2.68/1.46  Preprocessing        : 0.32
% 2.68/1.46  Parsing              : 0.17
% 2.68/1.46  CNF conversion       : 0.02
% 2.68/1.46  Main loop            : 0.36
% 2.68/1.46  Inferencing          : 0.14
% 2.68/1.46  Reduction            : 0.10
% 2.68/1.46  Demodulation         : 0.07
% 2.68/1.46  BG Simplification    : 0.02
% 2.68/1.46  Subsumption          : 0.06
% 2.68/1.46  Abstraction          : 0.02
% 2.68/1.46  MUC search           : 0.00
% 2.68/1.46  Cooper               : 0.00
% 2.68/1.46  Total                : 0.71
% 2.68/1.46  Index Insertion      : 0.00
% 2.68/1.46  Index Deletion       : 0.00
% 2.68/1.46  Index Matching       : 0.00
% 2.68/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
