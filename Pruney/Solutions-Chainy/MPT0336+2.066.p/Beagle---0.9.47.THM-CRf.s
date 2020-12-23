%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 10.16s
% Output     : CNFRefutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 170 expanded)
%              Number of leaves         :   35 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 251 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_91,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_32,plain,(
    ! [A_27,B_28] : r1_xboole_0(k4_xboole_0(A_27,B_28),B_28) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_117,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_27,B_28] : k3_xboole_0(k4_xboole_0(A_27,B_28),B_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_528,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,k3_xboole_0(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_534,plain,(
    ! [A_27,B_28,C_84] :
      ( ~ r1_xboole_0(k4_xboole_0(A_27,B_28),B_28)
      | ~ r2_hidden(C_84,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_528])).

tff(c_550,plain,(
    ! [C_84] : ~ r2_hidden(C_84,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_534])).

tff(c_68,plain,(
    ! [B_45,A_46] :
      ( r1_xboole_0(B_45,A_46)
      | ~ r1_xboole_0(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k4_xboole_0(A_27,B_28)) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_224,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = A_63
      | ~ r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_245,plain,(
    ! [B_28,A_27] : k4_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = B_28 ),
    inference(resolution,[status(thm)],[c_73,c_224])).

tff(c_130,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_117])).

tff(c_360,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_369,plain,(
    ! [B_28,A_27] : k4_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k5_xboole_0(B_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_360])).

tff(c_387,plain,(
    ! [B_28] : k5_xboole_0(B_28,k1_xboole_0) = B_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_369])).

tff(c_453,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_490,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k4_xboole_0(B_28,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_453])).

tff(c_581,plain,(
    ! [B_86] : k4_xboole_0(B_86,B_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_490])).

tff(c_599,plain,(
    ! [B_86] : k3_xboole_0(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_132])).

tff(c_52,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_133,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_1527,plain,(
    ! [A_134,B_135,C_136] : k3_xboole_0(k3_xboole_0(A_134,B_135),C_136) = k3_xboole_0(A_134,k3_xboole_0(B_135,C_136)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1596,plain,(
    ! [C_136] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_136)) = k3_xboole_0(k1_xboole_0,C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1527])).

tff(c_1622,plain,(
    ! [C_136] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_136)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_1596])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4728,plain,(
    ! [A_207,B_208] : k5_xboole_0(A_207,k3_xboole_0(B_208,A_207)) = k4_xboole_0(A_207,B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_360])).

tff(c_4768,plain,(
    ! [C_136] : k5_xboole_0(k3_xboole_0('#skF_4',C_136),k1_xboole_0) = k4_xboole_0(k3_xboole_0('#skF_4',C_136),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1622,c_4728])).

tff(c_4811,plain,(
    ! [C_136] : k4_xboole_0(k3_xboole_0('#skF_4',C_136),'#skF_5') = k3_xboole_0('#skF_4',C_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_4768])).

tff(c_56,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_57,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_627,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_xboole_0(A_88,k4_xboole_0(C_89,B_90))
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8620,plain,(
    ! [A_326,C_327,B_328] :
      ( k4_xboole_0(A_326,k4_xboole_0(C_327,B_328)) = A_326
      | ~ r1_tarski(A_326,B_328) ) ),
    inference(resolution,[status(thm)],[c_627,c_34])).

tff(c_24,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8801,plain,(
    ! [C_329,B_330] :
      ( k3_xboole_0(C_329,B_330) = C_329
      | ~ r1_tarski(C_329,B_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8620,c_24])).

tff(c_8805,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_8801])).

tff(c_405,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,k1_tarski(B_75)) = A_74
      | r2_hidden(B_75,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_429,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(A_76,k1_tarski(B_77))
      | r2_hidden(B_77,A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_32])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10225,plain,(
    ! [A_347,B_348] :
      ( k3_xboole_0(A_347,k1_tarski(B_348)) = k1_xboole_0
      | r2_hidden(B_348,A_347) ) ),
    inference(resolution,[status(thm)],[c_429,c_4])).

tff(c_10399,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8805,c_10225])).

tff(c_13613,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10399])).

tff(c_54,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1420,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ r1_xboole_0(A_128,B_129)
      | ~ r2_hidden(C_130,B_129)
      | ~ r2_hidden(C_130,A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_13183,plain,(
    ! [C_378,B_379,A_380] :
      ( ~ r2_hidden(C_378,B_379)
      | ~ r2_hidden(C_378,A_380)
      | k4_xboole_0(A_380,B_379) != A_380 ) ),
    inference(resolution,[status(thm)],[c_36,c_1420])).

tff(c_13201,plain,(
    ! [A_380] :
      ( ~ r2_hidden('#skF_6',A_380)
      | k4_xboole_0(A_380,'#skF_5') != A_380 ) ),
    inference(resolution,[status(thm)],[c_54,c_13183])).

tff(c_13619,plain,(
    k4_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_13613,c_13201])).

tff(c_13656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4811,c_13619])).

tff(c_13657,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10399])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_2'(A_12,B_13),k3_xboole_0(A_12,B_13))
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13773,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13657,c_16])).

tff(c_13836,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_13773])).

tff(c_74,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_68])).

tff(c_2279,plain,(
    ! [A_153,C_154,B_155] :
      ( ~ r1_xboole_0(A_153,C_154)
      | ~ r1_xboole_0(A_153,B_155)
      | r1_xboole_0(A_153,k2_xboole_0(B_155,C_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19489,plain,(
    ! [B_425,C_426,A_427] :
      ( r1_xboole_0(k2_xboole_0(B_425,C_426),A_427)
      | ~ r1_xboole_0(A_427,C_426)
      | ~ r1_xboole_0(A_427,B_425) ) ),
    inference(resolution,[status(thm)],[c_2279,c_8])).

tff(c_50,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_19519,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_19489,c_50])).

tff(c_19532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13836,c_74,c_19519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:55:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.16/3.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/3.69  
% 10.20/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/3.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.20/3.69  
% 10.20/3.69  %Foreground sorts:
% 10.20/3.69  
% 10.20/3.69  
% 10.20/3.69  %Background operators:
% 10.20/3.69  
% 10.20/3.69  
% 10.20/3.69  %Foreground operators:
% 10.20/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/3.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.20/3.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.20/3.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.20/3.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/3.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.20/3.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.20/3.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.20/3.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.20/3.69  tff('#skF_5', type, '#skF_5': $i).
% 10.20/3.69  tff('#skF_6', type, '#skF_6': $i).
% 10.20/3.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.20/3.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.20/3.69  tff('#skF_3', type, '#skF_3': $i).
% 10.20/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/3.69  tff('#skF_4', type, '#skF_4': $i).
% 10.20/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/3.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.20/3.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.20/3.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.20/3.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.20/3.69  
% 10.20/3.71  tff(f_91, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.20/3.71  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.20/3.71  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.20/3.71  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.20/3.71  tff(f_95, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.20/3.71  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.20/3.71  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.20/3.71  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 10.20/3.71  tff(f_71, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 10.20/3.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.20/3.71  tff(f_99, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 10.20/3.71  tff(f_110, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.20/3.71  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.20/3.71  tff(f_89, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 10.20/3.71  tff(c_32, plain, (![A_27, B_28]: (r1_xboole_0(k4_xboole_0(A_27, B_28), B_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.20/3.71  tff(c_117, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.20/3.71  tff(c_132, plain, (![A_27, B_28]: (k3_xboole_0(k4_xboole_0(A_27, B_28), B_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_117])).
% 10.20/3.71  tff(c_528, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, k3_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.20/3.71  tff(c_534, plain, (![A_27, B_28, C_84]: (~r1_xboole_0(k4_xboole_0(A_27, B_28), B_28) | ~r2_hidden(C_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_528])).
% 10.20/3.71  tff(c_550, plain, (![C_84]: (~r2_hidden(C_84, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_534])).
% 10.20/3.71  tff(c_68, plain, (![B_45, A_46]: (r1_xboole_0(B_45, A_46) | ~r1_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.20/3.71  tff(c_73, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k4_xboole_0(A_27, B_28)))), inference(resolution, [status(thm)], [c_32, c_68])).
% 10.20/3.71  tff(c_224, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=A_63 | ~r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.20/3.71  tff(c_245, plain, (![B_28, A_27]: (k4_xboole_0(B_28, k4_xboole_0(A_27, B_28))=B_28)), inference(resolution, [status(thm)], [c_73, c_224])).
% 10.20/3.71  tff(c_130, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_117])).
% 10.20/3.71  tff(c_360, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.20/3.71  tff(c_369, plain, (![B_28, A_27]: (k4_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k5_xboole_0(B_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_360])).
% 10.20/3.71  tff(c_387, plain, (![B_28]: (k5_xboole_0(B_28, k1_xboole_0)=B_28)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_369])).
% 10.20/3.71  tff(c_453, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.20/3.71  tff(c_490, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k4_xboole_0(B_28, B_28))), inference(superposition, [status(thm), theory('equality')], [c_245, c_453])).
% 10.20/3.71  tff(c_581, plain, (![B_86]: (k4_xboole_0(B_86, B_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_490])).
% 10.20/3.71  tff(c_599, plain, (![B_86]: (k3_xboole_0(k1_xboole_0, B_86)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_581, c_132])).
% 10.20/3.71  tff(c_52, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.20/3.71  tff(c_133, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_117])).
% 10.20/3.71  tff(c_1527, plain, (![A_134, B_135, C_136]: (k3_xboole_0(k3_xboole_0(A_134, B_135), C_136)=k3_xboole_0(A_134, k3_xboole_0(B_135, C_136)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.20/3.71  tff(c_1596, plain, (![C_136]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_136))=k3_xboole_0(k1_xboole_0, C_136))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1527])).
% 10.20/3.71  tff(c_1622, plain, (![C_136]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_136))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_599, c_1596])).
% 10.20/3.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.20/3.71  tff(c_4728, plain, (![A_207, B_208]: (k5_xboole_0(A_207, k3_xboole_0(B_208, A_207))=k4_xboole_0(A_207, B_208))), inference(superposition, [status(thm), theory('equality')], [c_2, c_360])).
% 10.20/3.71  tff(c_4768, plain, (![C_136]: (k5_xboole_0(k3_xboole_0('#skF_4', C_136), k1_xboole_0)=k4_xboole_0(k3_xboole_0('#skF_4', C_136), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1622, c_4728])).
% 10.20/3.71  tff(c_4811, plain, (![C_136]: (k4_xboole_0(k3_xboole_0('#skF_4', C_136), '#skF_5')=k3_xboole_0('#skF_4', C_136))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_4768])).
% 10.20/3.71  tff(c_56, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.20/3.71  tff(c_57, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 10.20/3.71  tff(c_627, plain, (![A_88, C_89, B_90]: (r1_xboole_0(A_88, k4_xboole_0(C_89, B_90)) | ~r1_tarski(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.20/3.71  tff(c_34, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.20/3.71  tff(c_8620, plain, (![A_326, C_327, B_328]: (k4_xboole_0(A_326, k4_xboole_0(C_327, B_328))=A_326 | ~r1_tarski(A_326, B_328))), inference(resolution, [status(thm)], [c_627, c_34])).
% 10.20/3.71  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.20/3.71  tff(c_8801, plain, (![C_329, B_330]: (k3_xboole_0(C_329, B_330)=C_329 | ~r1_tarski(C_329, B_330))), inference(superposition, [status(thm), theory('equality')], [c_8620, c_24])).
% 10.20/3.71  tff(c_8805, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_57, c_8801])).
% 10.20/3.71  tff(c_405, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k1_tarski(B_75))=A_74 | r2_hidden(B_75, A_74))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.20/3.71  tff(c_429, plain, (![A_76, B_77]: (r1_xboole_0(A_76, k1_tarski(B_77)) | r2_hidden(B_77, A_76))), inference(superposition, [status(thm), theory('equality')], [c_405, c_32])).
% 10.20/3.71  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.20/3.71  tff(c_10225, plain, (![A_347, B_348]: (k3_xboole_0(A_347, k1_tarski(B_348))=k1_xboole_0 | r2_hidden(B_348, A_347))), inference(resolution, [status(thm)], [c_429, c_4])).
% 10.20/3.71  tff(c_10399, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8805, c_10225])).
% 10.20/3.71  tff(c_13613, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_10399])).
% 10.20/3.71  tff(c_54, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.20/3.71  tff(c_36, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k4_xboole_0(A_29, B_30)!=A_29)), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.20/3.71  tff(c_1420, plain, (![A_128, B_129, C_130]: (~r1_xboole_0(A_128, B_129) | ~r2_hidden(C_130, B_129) | ~r2_hidden(C_130, A_128))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.20/3.71  tff(c_13183, plain, (![C_378, B_379, A_380]: (~r2_hidden(C_378, B_379) | ~r2_hidden(C_378, A_380) | k4_xboole_0(A_380, B_379)!=A_380)), inference(resolution, [status(thm)], [c_36, c_1420])).
% 10.20/3.71  tff(c_13201, plain, (![A_380]: (~r2_hidden('#skF_6', A_380) | k4_xboole_0(A_380, '#skF_5')!=A_380)), inference(resolution, [status(thm)], [c_54, c_13183])).
% 10.20/3.71  tff(c_13619, plain, (k4_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_13613, c_13201])).
% 10.20/3.71  tff(c_13656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4811, c_13619])).
% 10.20/3.71  tff(c_13657, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10399])).
% 10.20/3.71  tff(c_16, plain, (![A_12, B_13]: (r2_hidden('#skF_2'(A_12, B_13), k3_xboole_0(A_12, B_13)) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.20/3.71  tff(c_13773, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13657, c_16])).
% 10.20/3.71  tff(c_13836, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_550, c_13773])).
% 10.20/3.71  tff(c_74, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_68])).
% 10.20/3.71  tff(c_2279, plain, (![A_153, C_154, B_155]: (~r1_xboole_0(A_153, C_154) | ~r1_xboole_0(A_153, B_155) | r1_xboole_0(A_153, k2_xboole_0(B_155, C_154)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.20/3.71  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.20/3.71  tff(c_19489, plain, (![B_425, C_426, A_427]: (r1_xboole_0(k2_xboole_0(B_425, C_426), A_427) | ~r1_xboole_0(A_427, C_426) | ~r1_xboole_0(A_427, B_425))), inference(resolution, [status(thm)], [c_2279, c_8])).
% 10.20/3.71  tff(c_50, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.20/3.71  tff(c_19519, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_19489, c_50])).
% 10.20/3.71  tff(c_19532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13836, c_74, c_19519])).
% 10.20/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/3.71  
% 10.20/3.71  Inference rules
% 10.20/3.71  ----------------------
% 10.20/3.71  #Ref     : 1
% 10.20/3.71  #Sup     : 4915
% 10.20/3.71  #Fact    : 0
% 10.20/3.71  #Define  : 0
% 10.20/3.71  #Split   : 7
% 10.20/3.71  #Chain   : 0
% 10.20/3.71  #Close   : 0
% 10.20/3.71  
% 10.20/3.71  Ordering : KBO
% 10.20/3.71  
% 10.20/3.71  Simplification rules
% 10.20/3.71  ----------------------
% 10.20/3.71  #Subsume      : 1078
% 10.20/3.71  #Demod        : 3433
% 10.20/3.71  #Tautology    : 2592
% 10.20/3.71  #SimpNegUnit  : 151
% 10.20/3.71  #BackRed      : 5
% 10.20/3.71  
% 10.20/3.71  #Partial instantiations: 0
% 10.20/3.71  #Strategies tried      : 1
% 10.20/3.71  
% 10.20/3.71  Timing (in seconds)
% 10.20/3.71  ----------------------
% 10.20/3.71  Preprocessing        : 0.34
% 10.20/3.71  Parsing              : 0.18
% 10.20/3.71  CNF conversion       : 0.02
% 10.20/3.71  Main loop            : 2.60
% 10.20/3.71  Inferencing          : 0.56
% 10.20/3.71  Reduction            : 1.34
% 10.20/3.71  Demodulation         : 1.11
% 10.20/3.71  BG Simplification    : 0.06
% 10.20/3.71  Subsumption          : 0.49
% 10.20/3.71  Abstraction          : 0.08
% 10.20/3.71  MUC search           : 0.00
% 10.20/3.71  Cooper               : 0.00
% 10.20/3.71  Total                : 2.98
% 10.20/3.71  Index Insertion      : 0.00
% 10.20/3.71  Index Deletion       : 0.00
% 10.20/3.71  Index Matching       : 0.00
% 10.20/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
