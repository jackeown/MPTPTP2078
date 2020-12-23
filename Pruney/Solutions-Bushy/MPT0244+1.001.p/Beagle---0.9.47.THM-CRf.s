%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0244+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:58 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 172 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 320 expanded)
%              Number of equality atoms :   38 ( 206 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_37,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_12,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_8,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_18,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_25,plain,(
    ! [B_5,A_6] :
      ( k1_tarski(B_5) = A_6
      | k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_tarski(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_28,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_25])).

tff(c_38,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_22,c_28])).

tff(c_39,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_41,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_23])).

tff(c_4,plain,(
    ! [B_2] : r1_tarski(k1_tarski(B_2),k1_tarski(B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_49,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_55,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_49])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_55])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,k1_tarski(B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_61,plain,(
    ! [B_2] : r1_tarski('#skF_1',k1_tarski(B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_23])).

tff(c_69,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_71,plain,(
    ! [B_7,A_8] :
      ( k1_tarski(B_7) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_69,c_71])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_22,c_77])).

tff(c_90,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_10,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_111,plain,(
    ! [B_2] : r1_tarski('#skF_1',k1_tarski(B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_89])).

tff(c_119,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_122,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_89])).

tff(c_126,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_4])).

tff(c_134,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_126])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_134])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_14,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_14])).

tff(c_148,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_140,plain,(
    ! [B_2] : r1_tarski('#skF_3',k1_tarski(B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_6])).

tff(c_149,plain,(
    ! [B_2] : r1_tarski('#skF_1',k1_tarski(B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_140])).

tff(c_138,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_138])).

tff(c_163,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_165,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_138])).

tff(c_171,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_4])).

tff(c_177,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_171])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_177])).

%------------------------------------------------------------------------------
