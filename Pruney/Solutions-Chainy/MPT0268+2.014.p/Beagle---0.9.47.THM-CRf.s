%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 134 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 191 expanded)
%              Number of equality atoms :   46 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_86,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_44,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_218,plain,(
    ! [D_75,A_76,B_77] :
      ( r2_hidden(D_75,A_76)
      | ~ r2_hidden(D_75,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_490,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_107,B_108)),A_107)
      | k3_xboole_0(A_107,B_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_218])).

tff(c_203,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k4_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_345,plain,(
    ! [A_93,B_94] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_93,B_94)),B_94)
      | k4_xboole_0(A_93,B_94) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_203])).

tff(c_355,plain,(
    ! [A_19] :
      ( ~ r2_hidden('#skF_5'(A_19),k1_xboole_0)
      | k4_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_345])).

tff(c_357,plain,(
    ! [A_19] :
      ( ~ r2_hidden('#skF_5'(A_19),k1_xboole_0)
      | k1_xboole_0 = A_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_355])).

tff(c_530,plain,(
    ! [B_109] : k3_xboole_0(k1_xboole_0,B_109) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_490,c_357])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_187,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_196,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_187])).

tff(c_541,plain,(
    ! [B_109] : k5_xboole_0(B_109,k1_xboole_0) = k4_xboole_0(B_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_196])).

tff(c_569,plain,(
    ! [B_109] : k5_xboole_0(B_109,k1_xboole_0) = B_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_541])).

tff(c_229,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_76,B_77)),A_76)
      | k3_xboole_0(A_76,B_77) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_218])).

tff(c_182,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(k1_tarski(A_66),B_67)
      | r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_288,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(k1_tarski(A_89),B_90) = k1_tarski(A_89)
      | r2_hidden(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_182,c_46])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_875,plain,(
    ! [D_126,B_127,A_128] :
      ( ~ r2_hidden(D_126,B_127)
      | ~ r2_hidden(D_126,k1_tarski(A_128))
      | r2_hidden(A_128,B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_24])).

tff(c_1490,plain,(
    ! [A_161,A_162] :
      ( ~ r2_hidden('#skF_5'(A_161),k1_tarski(A_162))
      | r2_hidden(A_162,A_161)
      | k1_xboole_0 = A_161 ) ),
    inference(resolution,[status(thm)],[c_40,c_875])).

tff(c_16555,plain,(
    ! [A_5909,B_5910] :
      ( r2_hidden(A_5909,k3_xboole_0(k1_tarski(A_5909),B_5910))
      | k3_xboole_0(k1_tarski(A_5909),B_5910) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_229,c_1490])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16581,plain,(
    ! [A_5911,B_5912] :
      ( r2_hidden(A_5911,B_5912)
      | k3_xboole_0(k1_tarski(A_5911),B_5912) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16555,c_6])).

tff(c_16623,plain,(
    ! [B_5912,A_5911] :
      ( k4_xboole_0(B_5912,k1_tarski(A_5911)) = k5_xboole_0(B_5912,k1_xboole_0)
      | r2_hidden(A_5911,B_5912) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16581,c_196])).

tff(c_16660,plain,(
    ! [B_5913,A_5914] :
      ( k4_xboole_0(B_5913,k1_tarski(A_5914)) = B_5913
      | r2_hidden(A_5914,B_5913) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_16623])).

tff(c_84,plain,
    ( k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8'
    | r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_202,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_16697,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_16660,c_202])).

tff(c_16720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_16697])).

tff(c_16721,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_74,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_147,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_165,plain,(
    ! [B_57,A_58] : r2_hidden(B_57,k2_tarski(A_58,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_52])).

tff(c_168,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_165])).

tff(c_16722,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8'
    | k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16723,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_16729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16722,c_16723])).

tff(c_16730,plain,(
    k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_16780,plain,(
    ! [D_5924,B_5925,A_5926] :
      ( ~ r2_hidden(D_5924,B_5925)
      | ~ r2_hidden(D_5924,k4_xboole_0(A_5926,B_5925)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16801,plain,(
    ! [D_5929] :
      ( ~ r2_hidden(D_5929,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_5929,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16730,c_16780])).

tff(c_16805,plain,(
    ~ r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_168,c_16801])).

tff(c_16813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16721,c_16805])).

tff(c_16814,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_16870,plain,(
    ! [A_5948,B_5949] : k1_enumset1(A_5948,A_5948,B_5949) = k2_tarski(A_5948,B_5949) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16900,plain,(
    ! [B_5953,A_5954] : r2_hidden(B_5953,k2_tarski(A_5954,B_5953)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16870,c_52])).

tff(c_16903,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_16900])).

tff(c_16815,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16853,plain,(
    k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16815,c_90])).

tff(c_16888,plain,(
    ! [D_5950,B_5951,A_5952] :
      ( ~ r2_hidden(D_5950,B_5951)
      | ~ r2_hidden(D_5950,k4_xboole_0(A_5952,B_5951)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16918,plain,(
    ! [D_5960] :
      ( ~ r2_hidden(D_5960,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_5960,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16853,c_16888])).

tff(c_16922,plain,(
    ~ r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_16903,c_16918])).

tff(c_16930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16814,c_16922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.33/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.33/2.69  
% 7.33/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.33/2.69  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 7.33/2.69  
% 7.33/2.69  %Foreground sorts:
% 7.33/2.69  
% 7.33/2.69  
% 7.33/2.69  %Background operators:
% 7.33/2.69  
% 7.33/2.69  
% 7.33/2.69  %Foreground operators:
% 7.33/2.69  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.33/2.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.33/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.33/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.33/2.69  tff('#skF_11', type, '#skF_11': $i).
% 7.33/2.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.33/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.33/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.33/2.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.33/2.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.33/2.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.33/2.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.33/2.69  tff('#skF_10', type, '#skF_10': $i).
% 7.33/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.33/2.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.33/2.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.33/2.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.33/2.69  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.33/2.69  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.33/2.69  tff('#skF_9', type, '#skF_9': $i).
% 7.33/2.69  tff('#skF_8', type, '#skF_8': $i).
% 7.33/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.33/2.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.33/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.33/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.33/2.69  
% 7.47/2.71  tff(f_96, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.47/2.71  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.47/2.71  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.47/2.71  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.47/2.71  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.47/2.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.47/2.71  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.47/2.71  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.47/2.71  tff(f_62, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.47/2.71  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.47/2.71  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.47/2.71  tff(f_77, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.47/2.71  tff(c_86, plain, (~r2_hidden('#skF_9', '#skF_8') | r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.47/2.71  tff(c_109, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 7.47/2.71  tff(c_44, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.47/2.71  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.47/2.71  tff(c_218, plain, (![D_75, A_76, B_77]: (r2_hidden(D_75, A_76) | ~r2_hidden(D_75, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.47/2.71  tff(c_490, plain, (![A_107, B_108]: (r2_hidden('#skF_5'(k3_xboole_0(A_107, B_108)), A_107) | k3_xboole_0(A_107, B_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_218])).
% 7.47/2.71  tff(c_203, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k4_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.47/2.71  tff(c_345, plain, (![A_93, B_94]: (~r2_hidden('#skF_5'(k4_xboole_0(A_93, B_94)), B_94) | k4_xboole_0(A_93, B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_203])).
% 7.47/2.71  tff(c_355, plain, (![A_19]: (~r2_hidden('#skF_5'(A_19), k1_xboole_0) | k4_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_345])).
% 7.47/2.71  tff(c_357, plain, (![A_19]: (~r2_hidden('#skF_5'(A_19), k1_xboole_0) | k1_xboole_0=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_355])).
% 7.47/2.71  tff(c_530, plain, (![B_109]: (k3_xboole_0(k1_xboole_0, B_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_490, c_357])).
% 7.47/2.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.47/2.71  tff(c_187, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.47/2.71  tff(c_196, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_187])).
% 7.47/2.71  tff(c_541, plain, (![B_109]: (k5_xboole_0(B_109, k1_xboole_0)=k4_xboole_0(B_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_530, c_196])).
% 7.47/2.71  tff(c_569, plain, (![B_109]: (k5_xboole_0(B_109, k1_xboole_0)=B_109)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_541])).
% 7.47/2.71  tff(c_229, plain, (![A_76, B_77]: (r2_hidden('#skF_5'(k3_xboole_0(A_76, B_77)), A_76) | k3_xboole_0(A_76, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_218])).
% 7.47/2.71  tff(c_182, plain, (![A_66, B_67]: (r1_xboole_0(k1_tarski(A_66), B_67) | r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.47/2.71  tff(c_46, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.47/2.71  tff(c_288, plain, (![A_89, B_90]: (k4_xboole_0(k1_tarski(A_89), B_90)=k1_tarski(A_89) | r2_hidden(A_89, B_90))), inference(resolution, [status(thm)], [c_182, c_46])).
% 7.47/2.71  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.47/2.71  tff(c_875, plain, (![D_126, B_127, A_128]: (~r2_hidden(D_126, B_127) | ~r2_hidden(D_126, k1_tarski(A_128)) | r2_hidden(A_128, B_127))), inference(superposition, [status(thm), theory('equality')], [c_288, c_24])).
% 7.47/2.71  tff(c_1490, plain, (![A_161, A_162]: (~r2_hidden('#skF_5'(A_161), k1_tarski(A_162)) | r2_hidden(A_162, A_161) | k1_xboole_0=A_161)), inference(resolution, [status(thm)], [c_40, c_875])).
% 7.47/2.71  tff(c_16555, plain, (![A_5909, B_5910]: (r2_hidden(A_5909, k3_xboole_0(k1_tarski(A_5909), B_5910)) | k3_xboole_0(k1_tarski(A_5909), B_5910)=k1_xboole_0)), inference(resolution, [status(thm)], [c_229, c_1490])).
% 7.47/2.71  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.47/2.71  tff(c_16581, plain, (![A_5911, B_5912]: (r2_hidden(A_5911, B_5912) | k3_xboole_0(k1_tarski(A_5911), B_5912)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16555, c_6])).
% 7.47/2.71  tff(c_16623, plain, (![B_5912, A_5911]: (k4_xboole_0(B_5912, k1_tarski(A_5911))=k5_xboole_0(B_5912, k1_xboole_0) | r2_hidden(A_5911, B_5912))), inference(superposition, [status(thm), theory('equality')], [c_16581, c_196])).
% 7.47/2.71  tff(c_16660, plain, (![B_5913, A_5914]: (k4_xboole_0(B_5913, k1_tarski(A_5914))=B_5913 | r2_hidden(A_5914, B_5913))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_16623])).
% 7.47/2.71  tff(c_84, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8' | r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.47/2.71  tff(c_202, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_84])).
% 7.47/2.71  tff(c_16697, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_16660, c_202])).
% 7.47/2.71  tff(c_16720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_16697])).
% 7.47/2.71  tff(c_16721, plain, (r2_hidden('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_84])).
% 7.47/2.71  tff(c_74, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.47/2.71  tff(c_147, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.47/2.71  tff(c_52, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.47/2.71  tff(c_165, plain, (![B_57, A_58]: (r2_hidden(B_57, k2_tarski(A_58, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_52])).
% 7.47/2.71  tff(c_168, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_165])).
% 7.47/2.71  tff(c_16722, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(splitRight, [status(thm)], [c_84])).
% 7.47/2.71  tff(c_88, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8' | k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.47/2.71  tff(c_16723, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_88])).
% 7.47/2.71  tff(c_16729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16722, c_16723])).
% 7.47/2.71  tff(c_16730, plain, (k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(splitRight, [status(thm)], [c_88])).
% 7.47/2.71  tff(c_16780, plain, (![D_5924, B_5925, A_5926]: (~r2_hidden(D_5924, B_5925) | ~r2_hidden(D_5924, k4_xboole_0(A_5926, B_5925)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.47/2.71  tff(c_16801, plain, (![D_5929]: (~r2_hidden(D_5929, k1_tarski('#skF_11')) | ~r2_hidden(D_5929, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_16730, c_16780])).
% 7.47/2.71  tff(c_16805, plain, (~r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_168, c_16801])).
% 7.47/2.71  tff(c_16813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16721, c_16805])).
% 7.47/2.71  tff(c_16814, plain, (r2_hidden('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_86])).
% 7.47/2.71  tff(c_16870, plain, (![A_5948, B_5949]: (k1_enumset1(A_5948, A_5948, B_5949)=k2_tarski(A_5948, B_5949))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.47/2.71  tff(c_16900, plain, (![B_5953, A_5954]: (r2_hidden(B_5953, k2_tarski(A_5954, B_5953)))), inference(superposition, [status(thm), theory('equality')], [c_16870, c_52])).
% 7.47/2.71  tff(c_16903, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_16900])).
% 7.47/2.71  tff(c_16815, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 7.47/2.71  tff(c_90, plain, (~r2_hidden('#skF_9', '#skF_8') | k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.47/2.71  tff(c_16853, plain, (k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_16815, c_90])).
% 7.47/2.71  tff(c_16888, plain, (![D_5950, B_5951, A_5952]: (~r2_hidden(D_5950, B_5951) | ~r2_hidden(D_5950, k4_xboole_0(A_5952, B_5951)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.47/2.71  tff(c_16918, plain, (![D_5960]: (~r2_hidden(D_5960, k1_tarski('#skF_11')) | ~r2_hidden(D_5960, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_16853, c_16888])).
% 7.47/2.71  tff(c_16922, plain, (~r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_16903, c_16918])).
% 7.47/2.71  tff(c_16930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16814, c_16922])).
% 7.47/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.71  
% 7.47/2.71  Inference rules
% 7.47/2.71  ----------------------
% 7.47/2.71  #Ref     : 0
% 7.47/2.71  #Sup     : 3060
% 7.47/2.71  #Fact    : 2
% 7.47/2.71  #Define  : 0
% 7.47/2.71  #Split   : 3
% 7.47/2.71  #Chain   : 0
% 7.47/2.71  #Close   : 0
% 7.47/2.71  
% 7.47/2.71  Ordering : KBO
% 7.47/2.71  
% 7.47/2.71  Simplification rules
% 7.47/2.71  ----------------------
% 7.47/2.71  #Subsume      : 808
% 7.47/2.71  #Demod        : 681
% 7.47/2.71  #Tautology    : 219
% 7.47/2.71  #SimpNegUnit  : 1
% 7.47/2.71  #BackRed      : 0
% 7.47/2.71  
% 7.47/2.71  #Partial instantiations: 2680
% 7.47/2.71  #Strategies tried      : 1
% 7.47/2.71  
% 7.47/2.72  Timing (in seconds)
% 7.47/2.72  ----------------------
% 7.47/2.72  Preprocessing        : 0.32
% 7.47/2.72  Parsing              : 0.16
% 7.47/2.72  CNF conversion       : 0.03
% 7.47/2.72  Main loop            : 1.63
% 7.47/2.72  Inferencing          : 0.57
% 7.47/2.72  Reduction            : 0.48
% 7.47/2.72  Demodulation         : 0.35
% 7.47/2.72  BG Simplification    : 0.09
% 7.47/2.72  Subsumption          : 0.36
% 7.47/2.72  Abstraction          : 0.12
% 7.47/2.72  MUC search           : 0.00
% 7.47/2.72  Cooper               : 0.00
% 7.47/2.72  Total                : 1.99
% 7.47/2.72  Index Insertion      : 0.00
% 7.47/2.72  Index Deletion       : 0.00
% 7.47/2.72  Index Matching       : 0.00
% 7.47/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
