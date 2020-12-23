%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:58 EST 2020

% Result     : Theorem 6.53s
% Output     : CNFRefutation 6.53s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 297 expanded)
%              Number of leaves         :   32 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 440 expanded)
%              Number of equality atoms :   40 ( 200 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_77,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_50,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    k1_ordinal1('#skF_2') = k1_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_97,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_tarski(A_48)) = k1_ordinal1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [A_49] : r1_tarski(A_49,k1_ordinal1(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_12])).

tff(c_112,plain,(
    r1_tarski('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_109])).

tff(c_38,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_tarski(A_32)) = k1_ordinal1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_431,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(k4_xboole_0(A_93,B_94),C_95)
      | ~ r1_tarski(A_93,k2_xboole_0(B_94,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(B_26) = A_25
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_tarski(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1411,plain,(
    ! [A_203,B_204,B_205] :
      ( k4_xboole_0(A_203,B_204) = k1_tarski(B_205)
      | k4_xboole_0(A_203,B_204) = k1_xboole_0
      | ~ r1_tarski(A_203,k2_xboole_0(B_204,k1_tarski(B_205))) ) ),
    inference(resolution,[status(thm)],[c_431,c_24])).

tff(c_5314,plain,(
    ! [A_390,A_391] :
      ( k4_xboole_0(A_390,A_391) = k1_tarski(A_391)
      | k4_xboole_0(A_390,A_391) = k1_xboole_0
      | ~ r1_tarski(A_390,k1_ordinal1(A_391)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1411])).

tff(c_5357,plain,
    ( k4_xboole_0('#skF_2','#skF_1') = k1_tarski('#skF_1')
    | k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_5314])).

tff(c_5361,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5357])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k4_xboole_0(B_4,A_3) != k4_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5368,plain,
    ( '#skF_2' = '#skF_1'
    | k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5361,c_4])).

tff(c_5378,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5368])).

tff(c_103,plain,(
    ! [A_48] : r1_tarski(A_48,k1_ordinal1(A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_12])).

tff(c_5400,plain,(
    ! [A_394] :
      ( k4_xboole_0(A_394,'#skF_2') = k1_tarski('#skF_2')
      | k4_xboole_0(A_394,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_394,k1_ordinal1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_5314])).

tff(c_5430,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_5400])).

tff(c_5446,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_5378,c_5430])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5455,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5446,c_6])).

tff(c_16,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_312,plain,(
    ! [B_73,C_74,A_75] :
      ( r2_hidden(B_73,C_74)
      | ~ r1_tarski(k2_tarski(A_75,B_73),C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_333,plain,(
    ! [A_17,C_74] :
      ( r2_hidden(A_17,C_74)
      | ~ r1_tarski(k1_tarski(A_17),C_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_312])).

tff(c_5462,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_5455,c_333])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_5468,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5462,c_2])).

tff(c_14,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_166,plain,(
    ! [B_58,A_59] : k3_tarski(k2_tarski(B_58,A_59)) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_30,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_217,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_30])).

tff(c_256,plain,(
    ! [A_65,B_66] : r1_tarski(A_65,k2_xboole_0(B_66,A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_12])).

tff(c_272,plain,(
    ! [A_32] : r1_tarski(k1_tarski(A_32),k1_ordinal1(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_256])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(k1_tarski(A_23),B_24)
      | r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_531,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(A_107,B_108)
      | ~ r1_xboole_0(A_107,C_109)
      | ~ r1_tarski(A_107,k2_xboole_0(B_108,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1177,plain,(
    ! [A_181,A_182] :
      ( r1_tarski(A_181,A_182)
      | ~ r1_xboole_0(A_181,k1_tarski(A_182))
      | ~ r1_tarski(A_181,k1_ordinal1(A_182)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_531])).

tff(c_5470,plain,(
    ! [A_395,A_396] :
      ( r1_tarski(k1_tarski(A_395),A_396)
      | ~ r1_tarski(k1_tarski(A_395),k1_ordinal1(A_396))
      | r2_hidden(A_395,k1_tarski(A_396)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1177])).

tff(c_5553,plain,(
    ! [A_398] :
      ( r1_tarski(k1_tarski(A_398),'#skF_2')
      | ~ r1_tarski(k1_tarski(A_398),k1_ordinal1('#skF_1'))
      | r2_hidden(A_398,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_5470])).

tff(c_5576,plain,
    ( r1_tarski(k1_tarski('#skF_1'),'#skF_2')
    | r2_hidden('#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_272,c_5553])).

tff(c_5577,plain,(
    r2_hidden('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5576])).

tff(c_40,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5587,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5577,c_40])).

tff(c_5594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5455,c_5587])).

tff(c_5595,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5576])).

tff(c_5599,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5595,c_333])).

tff(c_5603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5468,c_5599])).

tff(c_5604,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5357])).

tff(c_5619,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5604,c_6])).

tff(c_5666,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5619,c_333])).

tff(c_5672,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_5666,c_2])).

tff(c_278,plain,(
    ! [A_67] : r1_tarski(k1_tarski(A_67),k1_ordinal1(A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_256])).

tff(c_281,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_278])).

tff(c_5838,plain,(
    ! [A_411,A_412] :
      ( r1_tarski(k1_tarski(A_411),A_412)
      | ~ r1_tarski(k1_tarski(A_411),k1_ordinal1(A_412))
      | r2_hidden(A_411,k1_tarski(A_412)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1177])).

tff(c_5862,plain,
    ( r1_tarski(k1_tarski('#skF_2'),'#skF_1')
    | r2_hidden('#skF_2',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_281,c_5838])).

tff(c_5868,plain,(
    r2_hidden('#skF_2',k1_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5862])).

tff(c_5878,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5868,c_40])).

tff(c_5885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5619,c_5878])).

tff(c_5886,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5862])).

tff(c_5890,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_5886,c_333])).

tff(c_5894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5672,c_5890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.53/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.53/2.37  
% 6.53/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.53/2.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.53/2.38  
% 6.53/2.38  %Foreground sorts:
% 6.53/2.38  
% 6.53/2.38  
% 6.53/2.38  %Background operators:
% 6.53/2.38  
% 6.53/2.38  
% 6.53/2.38  %Foreground operators:
% 6.53/2.38  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.53/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.53/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.53/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.53/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.53/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.53/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.53/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.53/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.53/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.53/2.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.53/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.53/2.38  tff('#skF_1', type, '#skF_1': $i).
% 6.53/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.53/2.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.53/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.53/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.53/2.38  
% 6.53/2.39  tff(f_87, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 6.53/2.39  tff(f_77, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.53/2.39  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.53/2.39  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.53/2.39  tff(f_67, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.53/2.39  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 6.53/2.39  tff(f_36, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.53/2.39  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.53/2.39  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.53/2.39  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 6.53/2.39  tff(f_50, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.53/2.39  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.53/2.39  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.53/2.39  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 6.53/2.39  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.53/2.39  tff(c_42, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.53/2.39  tff(c_44, plain, (k1_ordinal1('#skF_2')=k1_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.53/2.39  tff(c_97, plain, (![A_48]: (k2_xboole_0(A_48, k1_tarski(A_48))=k1_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.53/2.39  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.53/2.39  tff(c_109, plain, (![A_49]: (r1_tarski(A_49, k1_ordinal1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_12])).
% 6.53/2.39  tff(c_112, plain, (r1_tarski('#skF_2', k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_109])).
% 6.53/2.39  tff(c_38, plain, (![A_32]: (k2_xboole_0(A_32, k1_tarski(A_32))=k1_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.53/2.39  tff(c_431, plain, (![A_93, B_94, C_95]: (r1_tarski(k4_xboole_0(A_93, B_94), C_95) | ~r1_tarski(A_93, k2_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.53/2.39  tff(c_24, plain, (![B_26, A_25]: (k1_tarski(B_26)=A_25 | k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_tarski(B_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.53/2.39  tff(c_1411, plain, (![A_203, B_204, B_205]: (k4_xboole_0(A_203, B_204)=k1_tarski(B_205) | k4_xboole_0(A_203, B_204)=k1_xboole_0 | ~r1_tarski(A_203, k2_xboole_0(B_204, k1_tarski(B_205))))), inference(resolution, [status(thm)], [c_431, c_24])).
% 6.53/2.39  tff(c_5314, plain, (![A_390, A_391]: (k4_xboole_0(A_390, A_391)=k1_tarski(A_391) | k4_xboole_0(A_390, A_391)=k1_xboole_0 | ~r1_tarski(A_390, k1_ordinal1(A_391)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1411])).
% 6.53/2.39  tff(c_5357, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_tarski('#skF_1') | k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_5314])).
% 6.53/2.39  tff(c_5361, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5357])).
% 6.53/2.39  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | k4_xboole_0(B_4, A_3)!=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.53/2.39  tff(c_5368, plain, ('#skF_2'='#skF_1' | k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5361, c_4])).
% 6.53/2.39  tff(c_5378, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_5368])).
% 6.53/2.39  tff(c_103, plain, (![A_48]: (r1_tarski(A_48, k1_ordinal1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_12])).
% 6.53/2.39  tff(c_5400, plain, (![A_394]: (k4_xboole_0(A_394, '#skF_2')=k1_tarski('#skF_2') | k4_xboole_0(A_394, '#skF_2')=k1_xboole_0 | ~r1_tarski(A_394, k1_ordinal1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_5314])).
% 6.53/2.39  tff(c_5430, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_2') | k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_5400])).
% 6.53/2.39  tff(c_5446, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_5378, c_5430])).
% 6.53/2.39  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.53/2.39  tff(c_5455, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5446, c_6])).
% 6.53/2.39  tff(c_16, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.53/2.39  tff(c_312, plain, (![B_73, C_74, A_75]: (r2_hidden(B_73, C_74) | ~r1_tarski(k2_tarski(A_75, B_73), C_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.53/2.39  tff(c_333, plain, (![A_17, C_74]: (r2_hidden(A_17, C_74) | ~r1_tarski(k1_tarski(A_17), C_74))), inference(superposition, [status(thm), theory('equality')], [c_16, c_312])).
% 6.53/2.39  tff(c_5462, plain, (r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_5455, c_333])).
% 6.53/2.39  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.53/2.39  tff(c_5468, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5462, c_2])).
% 6.53/2.39  tff(c_14, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.53/2.39  tff(c_123, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.53/2.39  tff(c_166, plain, (![B_58, A_59]: (k3_tarski(k2_tarski(B_58, A_59))=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 6.53/2.39  tff(c_30, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.53/2.39  tff(c_217, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_166, c_30])).
% 6.53/2.39  tff(c_256, plain, (![A_65, B_66]: (r1_tarski(A_65, k2_xboole_0(B_66, A_65)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_12])).
% 6.53/2.39  tff(c_272, plain, (![A_32]: (r1_tarski(k1_tarski(A_32), k1_ordinal1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_256])).
% 6.53/2.39  tff(c_22, plain, (![A_23, B_24]: (r1_xboole_0(k1_tarski(A_23), B_24) | r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.53/2.39  tff(c_531, plain, (![A_107, B_108, C_109]: (r1_tarski(A_107, B_108) | ~r1_xboole_0(A_107, C_109) | ~r1_tarski(A_107, k2_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.53/2.39  tff(c_1177, plain, (![A_181, A_182]: (r1_tarski(A_181, A_182) | ~r1_xboole_0(A_181, k1_tarski(A_182)) | ~r1_tarski(A_181, k1_ordinal1(A_182)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_531])).
% 6.53/2.39  tff(c_5470, plain, (![A_395, A_396]: (r1_tarski(k1_tarski(A_395), A_396) | ~r1_tarski(k1_tarski(A_395), k1_ordinal1(A_396)) | r2_hidden(A_395, k1_tarski(A_396)))), inference(resolution, [status(thm)], [c_22, c_1177])).
% 6.53/2.39  tff(c_5553, plain, (![A_398]: (r1_tarski(k1_tarski(A_398), '#skF_2') | ~r1_tarski(k1_tarski(A_398), k1_ordinal1('#skF_1')) | r2_hidden(A_398, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_5470])).
% 6.53/2.39  tff(c_5576, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2') | r2_hidden('#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_272, c_5553])).
% 6.53/2.39  tff(c_5577, plain, (r2_hidden('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_5576])).
% 6.53/2.39  tff(c_40, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.53/2.39  tff(c_5587, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_5577, c_40])).
% 6.53/2.39  tff(c_5594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5455, c_5587])).
% 6.53/2.39  tff(c_5595, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_5576])).
% 6.53/2.39  tff(c_5599, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5595, c_333])).
% 6.53/2.39  tff(c_5603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5468, c_5599])).
% 6.53/2.39  tff(c_5604, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_5357])).
% 6.53/2.39  tff(c_5619, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5604, c_6])).
% 6.53/2.39  tff(c_5666, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5619, c_333])).
% 6.53/2.39  tff(c_5672, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_5666, c_2])).
% 6.53/2.39  tff(c_278, plain, (![A_67]: (r1_tarski(k1_tarski(A_67), k1_ordinal1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_256])).
% 6.53/2.39  tff(c_281, plain, (r1_tarski(k1_tarski('#skF_2'), k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_278])).
% 6.53/2.39  tff(c_5838, plain, (![A_411, A_412]: (r1_tarski(k1_tarski(A_411), A_412) | ~r1_tarski(k1_tarski(A_411), k1_ordinal1(A_412)) | r2_hidden(A_411, k1_tarski(A_412)))), inference(resolution, [status(thm)], [c_22, c_1177])).
% 6.53/2.39  tff(c_5862, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1') | r2_hidden('#skF_2', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_281, c_5838])).
% 6.53/2.39  tff(c_5868, plain, (r2_hidden('#skF_2', k1_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_5862])).
% 6.53/2.39  tff(c_5878, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_5868, c_40])).
% 6.53/2.39  tff(c_5885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5619, c_5878])).
% 6.53/2.39  tff(c_5886, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_5862])).
% 6.53/2.39  tff(c_5890, plain, (r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_5886, c_333])).
% 6.53/2.39  tff(c_5894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5672, c_5890])).
% 6.53/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.53/2.39  
% 6.53/2.39  Inference rules
% 6.53/2.39  ----------------------
% 6.53/2.39  #Ref     : 1
% 6.53/2.39  #Sup     : 1396
% 6.53/2.39  #Fact    : 8
% 6.53/2.39  #Define  : 0
% 6.53/2.39  #Split   : 18
% 6.53/2.39  #Chain   : 0
% 6.53/2.39  #Close   : 0
% 6.53/2.39  
% 6.53/2.39  Ordering : KBO
% 6.53/2.39  
% 6.53/2.39  Simplification rules
% 6.53/2.39  ----------------------
% 6.53/2.39  #Subsume      : 301
% 6.53/2.39  #Demod        : 506
% 6.53/2.39  #Tautology    : 385
% 6.53/2.39  #SimpNegUnit  : 67
% 6.53/2.39  #BackRed      : 24
% 6.53/2.39  
% 6.53/2.39  #Partial instantiations: 0
% 6.53/2.39  #Strategies tried      : 1
% 6.53/2.39  
% 6.53/2.39  Timing (in seconds)
% 6.53/2.39  ----------------------
% 6.53/2.40  Preprocessing        : 0.33
% 6.53/2.40  Parsing              : 0.18
% 6.53/2.40  CNF conversion       : 0.02
% 6.53/2.40  Main loop            : 1.24
% 6.53/2.40  Inferencing          : 0.37
% 6.53/2.40  Reduction            : 0.48
% 6.53/2.40  Demodulation         : 0.34
% 6.53/2.40  BG Simplification    : 0.04
% 6.53/2.40  Subsumption          : 0.25
% 6.53/2.40  Abstraction          : 0.04
% 6.53/2.40  MUC search           : 0.00
% 6.53/2.40  Cooper               : 0.00
% 6.53/2.40  Total                : 1.61
% 6.53/2.40  Index Insertion      : 0.00
% 6.53/2.40  Index Deletion       : 0.00
% 6.53/2.40  Index Matching       : 0.00
% 6.53/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
