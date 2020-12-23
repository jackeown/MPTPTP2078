%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 236 expanded)
%              Number of leaves         :   24 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 415 expanded)
%              Number of equality atoms :   66 ( 225 expanded)
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

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_56,axiom,(
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

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(k1_tarski(A_18),B_19) = k1_xboole_0
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_152,plain,(
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

tff(c_222,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(k1_tarski(A_51),B_52) = k1_xboole_0
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_204,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_206,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_204,c_4])).

tff(c_212,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_206])).

tff(c_217,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_212])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_217])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_153,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,k1_tarski(A_44))
      | r2_hidden(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_275,plain,(
    ! [B_57,A_58] :
      ( k4_xboole_0(B_57,k1_tarski(A_58)) = B_57
      | r2_hidden(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_174,c_16])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_12])).

tff(c_285,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_213])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_64,c_285])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_328,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_161,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_165,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_329,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_165])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_329])).

tff(c_334,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_322])).

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

tff(c_359,plain,(
    ! [A_60] : r1_xboole_0('#skF_1',A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_58])).

tff(c_365,plain,(
    ! [A_60] : k4_xboole_0('#skF_1',A_60) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_359,c_16])).

tff(c_423,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | k4_xboole_0(A_64,B_65) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_10])).

tff(c_431,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_423,c_161])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_431])).

tff(c_438,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_472,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_476,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_438,c_472])).

tff(c_484,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_476])).

tff(c_493,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_484])).

tff(c_524,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_493])).

tff(c_464,plain,(
    ! [B_68,A_69] :
      ( r1_xboole_0(B_68,k1_tarski(A_69))
      | r2_hidden(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_556,plain,(
    ! [B_79,A_80] :
      ( k4_xboole_0(B_79,k1_tarski(A_80)) = B_79
      | r2_hidden(A_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_464,c_16])).

tff(c_443,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_438,c_12])).

tff(c_573,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_443])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_64,c_573])).

tff(c_608,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_609,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_609])).

tff(c_616,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_627,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_607,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_628,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_607])).

tff(c_631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_628])).

tff(c_632,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_65,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_637,plain,(
    ! [A_7] : k4_xboole_0('#skF_1',A_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_632,c_72])).

tff(c_626,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_607])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_632,c_626])).

tff(c_734,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_752,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_734,c_38])).

tff(c_753,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_735,plain,(
    ! [A_7] : r1_xboole_0('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_58])).

tff(c_754,plain,(
    ! [A_7] : r1_xboole_0('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_735])).

tff(c_817,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = A_103
      | ~ r1_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_832,plain,(
    ! [A_7] : k4_xboole_0('#skF_1',A_7) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_754,c_817])).

tff(c_756,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_734])).

tff(c_781,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | k4_xboole_0(A_94,B_95) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_10])).

tff(c_733,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_785,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_781,c_733])).

tff(c_855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_785])).

tff(c_856,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_858,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_733])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/2.14  
% 3.16/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/2.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.16/2.14  
% 3.16/2.14  %Foreground sorts:
% 3.16/2.14  
% 3.16/2.14  
% 3.16/2.14  %Background operators:
% 3.16/2.14  
% 3.16/2.14  
% 3.16/2.14  %Foreground operators:
% 3.16/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/2.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/2.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/2.14  tff('#skF_2', type, '#skF_2': $i).
% 3.16/2.14  tff('#skF_3', type, '#skF_3': $i).
% 3.16/2.14  tff('#skF_1', type, '#skF_1': $i).
% 3.16/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/2.14  tff('#skF_4', type, '#skF_4': $i).
% 3.16/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/2.14  
% 3.16/2.19  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/2.19  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.16/2.19  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.16/2.19  tff(f_67, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.16/2.19  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.16/2.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.16/2.19  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.16/2.19  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.16/2.19  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/2.19  tff(c_30, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), B_19)=k1_xboole_0 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/2.19  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/2.19  tff(c_32, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/2.19  tff(c_152, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 3.16/2.19  tff(c_100, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/2.19  tff(c_104, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_100])).
% 3.16/2.19  tff(c_222, plain, (![A_51, B_52]: (k4_xboole_0(k1_tarski(A_51), B_52)=k1_xboole_0 | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/2.19  tff(c_42, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/2.19  tff(c_204, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.16/2.19  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/2.19  tff(c_206, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_204, c_4])).
% 3.16/2.19  tff(c_212, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_152, c_206])).
% 3.16/2.19  tff(c_217, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_212])).
% 3.16/2.19  tff(c_252, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_222, c_217])).
% 3.16/2.19  tff(c_36, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/2.19  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 3.16/2.19  tff(c_153, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/2.19  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/2.19  tff(c_174, plain, (![B_43, A_44]: (r1_xboole_0(B_43, k1_tarski(A_44)) | r2_hidden(A_44, B_43))), inference(resolution, [status(thm)], [c_153, c_2])).
% 3.16/2.19  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/2.19  tff(c_275, plain, (![B_57, A_58]: (k4_xboole_0(B_57, k1_tarski(A_58))=B_57 | r2_hidden(A_58, B_57))), inference(resolution, [status(thm)], [c_174, c_16])).
% 3.16/2.19  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/2.19  tff(c_213, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_12])).
% 3.16/2.19  tff(c_285, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_275, c_213])).
% 3.16/2.19  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_64, c_285])).
% 3.16/2.19  tff(c_322, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 3.16/2.19  tff(c_328, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_322])).
% 3.16/2.19  tff(c_40, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/2.19  tff(c_161, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.16/2.19  tff(c_165, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_161])).
% 3.16/2.19  tff(c_329, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_328, c_165])).
% 3.16/2.19  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_329])).
% 3.16/2.19  tff(c_334, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_322])).
% 3.16/2.19  tff(c_14, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/2.19  tff(c_55, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/2.19  tff(c_58, plain, (![A_7]: (r1_xboole_0(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_14, c_55])).
% 3.16/2.19  tff(c_359, plain, (![A_60]: (r1_xboole_0('#skF_1', A_60))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_58])).
% 3.16/2.19  tff(c_365, plain, (![A_60]: (k4_xboole_0('#skF_1', A_60)='#skF_1')), inference(resolution, [status(thm)], [c_359, c_16])).
% 3.16/2.19  tff(c_423, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | k4_xboole_0(A_64, B_65)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_10])).
% 3.16/2.19  tff(c_431, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_423, c_161])).
% 3.16/2.19  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_365, c_431])).
% 3.16/2.19  tff(c_438, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 3.16/2.19  tff(c_472, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/2.19  tff(c_476, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_438, c_472])).
% 3.16/2.19  tff(c_484, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_152, c_476])).
% 3.16/2.19  tff(c_493, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_484])).
% 3.16/2.19  tff(c_524, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_493])).
% 3.16/2.19  tff(c_464, plain, (![B_68, A_69]: (r1_xboole_0(B_68, k1_tarski(A_69)) | r2_hidden(A_69, B_68))), inference(resolution, [status(thm)], [c_153, c_2])).
% 3.16/2.19  tff(c_556, plain, (![B_79, A_80]: (k4_xboole_0(B_79, k1_tarski(A_80))=B_79 | r2_hidden(A_80, B_79))), inference(resolution, [status(thm)], [c_464, c_16])).
% 3.16/2.19  tff(c_443, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_438, c_12])).
% 3.16/2.19  tff(c_573, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_556, c_443])).
% 3.16/2.19  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_64, c_573])).
% 3.16/2.19  tff(c_608, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.16/2.19  tff(c_34, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/2.19  tff(c_609, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 3.16/2.19  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_608, c_609])).
% 3.16/2.19  tff(c_616, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 3.16/2.19  tff(c_627, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_616])).
% 3.16/2.19  tff(c_607, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 3.16/2.19  tff(c_628, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_607])).
% 3.16/2.19  tff(c_631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_628])).
% 3.16/2.19  tff(c_632, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_616])).
% 3.16/2.19  tff(c_65, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/2.19  tff(c_72, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_65])).
% 3.16/2.19  tff(c_637, plain, (![A_7]: (k4_xboole_0('#skF_1', A_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_632, c_72])).
% 3.16/2.19  tff(c_626, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_607])).
% 3.16/2.19  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_637, c_632, c_626])).
% 3.16/2.19  tff(c_734, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.16/2.19  tff(c_38, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/2.19  tff(c_752, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_734, c_734, c_38])).
% 3.16/2.19  tff(c_753, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_752])).
% 3.16/2.19  tff(c_735, plain, (![A_7]: (r1_xboole_0('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_734, c_58])).
% 3.16/2.19  tff(c_754, plain, (![A_7]: (r1_xboole_0('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_753, c_735])).
% 3.16/2.19  tff(c_817, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=A_103 | ~r1_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/2.19  tff(c_832, plain, (![A_7]: (k4_xboole_0('#skF_1', A_7)='#skF_1')), inference(resolution, [status(thm)], [c_754, c_817])).
% 3.16/2.19  tff(c_756, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_734])).
% 3.16/2.19  tff(c_781, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | k4_xboole_0(A_94, B_95)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_756, c_10])).
% 3.16/2.19  tff(c_733, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 3.16/2.19  tff(c_785, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_781, c_733])).
% 3.16/2.19  tff(c_855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_832, c_785])).
% 3.16/2.19  tff(c_856, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_752])).
% 3.16/2.19  tff(c_858, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_856, c_733])).
% 3.16/2.19  tff(c_861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_858])).
% 3.16/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/2.19  
% 3.16/2.19  Inference rules
% 3.16/2.19  ----------------------
% 3.16/2.19  #Ref     : 0
% 3.16/2.19  #Sup     : 179
% 3.16/2.19  #Fact    : 0
% 3.16/2.19  #Define  : 0
% 3.16/2.19  #Split   : 9
% 3.16/2.19  #Chain   : 0
% 3.16/2.19  #Close   : 0
% 3.16/2.19  
% 3.16/2.19  Ordering : KBO
% 3.16/2.19  
% 3.16/2.19  Simplification rules
% 3.16/2.19  ----------------------
% 3.16/2.19  #Subsume      : 12
% 3.16/2.19  #Demod        : 72
% 3.16/2.19  #Tautology    : 108
% 3.16/2.19  #SimpNegUnit  : 6
% 3.16/2.19  #BackRed      : 29
% 3.16/2.19  
% 3.16/2.19  #Partial instantiations: 0
% 3.16/2.19  #Strategies tried      : 1
% 3.16/2.19  
% 3.16/2.19  Timing (in seconds)
% 3.16/2.19  ----------------------
% 3.16/2.20  Preprocessing        : 0.53
% 3.16/2.20  Parsing              : 0.30
% 3.16/2.20  CNF conversion       : 0.04
% 3.16/2.20  Main loop            : 0.61
% 3.16/2.20  Inferencing          : 0.24
% 3.16/2.20  Reduction            : 0.17
% 3.16/2.20  Demodulation         : 0.13
% 3.16/2.20  BG Simplification    : 0.03
% 3.16/2.20  Subsumption          : 0.11
% 3.16/2.20  Abstraction          : 0.02
% 3.16/2.20  MUC search           : 0.00
% 3.16/2.20  Cooper               : 0.00
% 3.16/2.20  Total                : 1.26
% 3.16/2.20  Index Insertion      : 0.00
% 3.16/2.20  Index Deletion       : 0.00
% 3.16/2.20  Index Matching       : 0.00
% 3.16/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
