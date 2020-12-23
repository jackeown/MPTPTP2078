%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 189 expanded)
%              Number of equality atoms :   20 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_46,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_150,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_414,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_430,plain,(
    ! [C_76] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_76,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_414])).

tff(c_446,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_430])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2021,plain,(
    ! [A_134,B_135,C_136] :
      ( ~ r1_xboole_0(A_134,k3_xboole_0(B_135,C_136))
      | ~ r1_tarski(A_134,C_136)
      | r1_xboole_0(A_134,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2083,plain,(
    ! [A_134] :
      ( ~ r1_xboole_0(A_134,k1_xboole_0)
      | ~ r1_tarski(A_134,'#skF_4')
      | r1_xboole_0(A_134,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2021])).

tff(c_2119,plain,(
    ! [A_137] :
      ( ~ r1_tarski(A_137,'#skF_4')
      | r1_xboole_0(A_137,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2083])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2298,plain,(
    ! [A_150] :
      ( k3_xboole_0(A_150,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_150,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2119,c_4])).

tff(c_2806,plain,(
    ! [B_165] : k3_xboole_0(k3_xboole_0('#skF_4',B_165),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2298])).

tff(c_2928,plain,(
    ! [B_165] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',B_165)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2806])).

tff(c_50,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_51,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_128,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_139,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_128])).

tff(c_333,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(k1_tarski(A_63),B_64)
      | r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_946,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(k1_tarski(A_106),B_107) = k1_xboole_0
      | r2_hidden(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_333,c_4])).

tff(c_1084,plain,(
    ! [B_112,A_113] :
      ( k3_xboole_0(B_112,k1_tarski(A_113)) = k1_xboole_0
      | r2_hidden(A_113,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_2])).

tff(c_1158,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1084])).

tff(c_2315,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1158])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_741,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,B_90)
      | ~ r2_hidden(C_91,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3378,plain,(
    ! [C_170,B_171,A_172] :
      ( ~ r2_hidden(C_170,B_171)
      | ~ r2_hidden(C_170,A_172)
      | k3_xboole_0(A_172,B_171) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_741])).

tff(c_3406,plain,(
    ! [A_173] :
      ( ~ r2_hidden('#skF_6',A_173)
      | k3_xboole_0(A_173,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_3378])).

tff(c_3413,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2315,c_3406])).

tff(c_3426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2928,c_2,c_3413])).

tff(c_3427,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1158])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_2'(A_12,B_13),k3_xboole_0(A_12,B_13))
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3455,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3427,c_16])).

tff(c_3504,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_3455])).

tff(c_111,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,A_47)
      | ~ r1_xboole_0(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_111])).

tff(c_1791,plain,(
    ! [A_127,C_128,B_129] :
      ( ~ r1_xboole_0(A_127,C_128)
      | ~ r1_xboole_0(A_127,B_129)
      | r1_xboole_0(A_127,k2_xboole_0(B_129,C_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5174,plain,(
    ! [B_216,C_217,A_218] :
      ( r1_xboole_0(k2_xboole_0(B_216,C_217),A_218)
      | ~ r1_xboole_0(A_218,C_217)
      | ~ r1_xboole_0(A_218,B_216) ) ),
    inference(resolution,[status(thm)],[c_1791,c_8])).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5200,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_5174,c_44])).

tff(c_5214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3504,c_117,c_5200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:33:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.89  
% 4.67/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.67/1.90  
% 4.67/1.90  %Foreground sorts:
% 4.67/1.90  
% 4.67/1.90  
% 4.67/1.90  %Background operators:
% 4.67/1.90  
% 4.67/1.90  
% 4.67/1.90  %Foreground operators:
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.67/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.67/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.67/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.67/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.67/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.67/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.67/1.90  
% 4.67/1.91  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.67/1.91  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.67/1.91  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.67/1.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.67/1.91  tff(f_69, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.67/1.91  tff(f_75, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.67/1.91  tff(f_99, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.67/1.91  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.67/1.91  tff(f_110, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.67/1.91  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.67/1.91  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.67/1.91  tff(f_91, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.67/1.91  tff(c_46, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.91  tff(c_150, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.91  tff(c_166, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_150])).
% 4.67/1.91  tff(c_414, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.91  tff(c_430, plain, (![C_76]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_166, c_414])).
% 4.67/1.91  tff(c_446, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_430])).
% 4.67/1.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.67/1.91  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.67/1.91  tff(c_24, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.67/1.91  tff(c_2021, plain, (![A_134, B_135, C_136]: (~r1_xboole_0(A_134, k3_xboole_0(B_135, C_136)) | ~r1_tarski(A_134, C_136) | r1_xboole_0(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.67/1.91  tff(c_2083, plain, (![A_134]: (~r1_xboole_0(A_134, k1_xboole_0) | ~r1_tarski(A_134, '#skF_4') | r1_xboole_0(A_134, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_2021])).
% 4.67/1.91  tff(c_2119, plain, (![A_137]: (~r1_tarski(A_137, '#skF_4') | r1_xboole_0(A_137, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2083])).
% 4.67/1.91  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.91  tff(c_2298, plain, (![A_150]: (k3_xboole_0(A_150, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_150, '#skF_4'))), inference(resolution, [status(thm)], [c_2119, c_4])).
% 4.67/1.91  tff(c_2806, plain, (![B_165]: (k3_xboole_0(k3_xboole_0('#skF_4', B_165), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_2298])).
% 4.67/1.91  tff(c_2928, plain, (![B_165]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', B_165))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2806])).
% 4.67/1.91  tff(c_50, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.91  tff(c_51, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 4.67/1.91  tff(c_128, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.67/1.91  tff(c_139, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_128])).
% 4.67/1.91  tff(c_333, plain, (![A_63, B_64]: (r1_xboole_0(k1_tarski(A_63), B_64) | r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.67/1.91  tff(c_946, plain, (![A_106, B_107]: (k3_xboole_0(k1_tarski(A_106), B_107)=k1_xboole_0 | r2_hidden(A_106, B_107))), inference(resolution, [status(thm)], [c_333, c_4])).
% 4.67/1.91  tff(c_1084, plain, (![B_112, A_113]: (k3_xboole_0(B_112, k1_tarski(A_113))=k1_xboole_0 | r2_hidden(A_113, B_112))), inference(superposition, [status(thm), theory('equality')], [c_946, c_2])).
% 4.67/1.91  tff(c_1158, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1084])).
% 4.67/1.91  tff(c_2315, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1158])).
% 4.67/1.91  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.91  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.91  tff(c_741, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, B_90) | ~r2_hidden(C_91, A_89))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/1.91  tff(c_3378, plain, (![C_170, B_171, A_172]: (~r2_hidden(C_170, B_171) | ~r2_hidden(C_170, A_172) | k3_xboole_0(A_172, B_171)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_741])).
% 4.67/1.91  tff(c_3406, plain, (![A_173]: (~r2_hidden('#skF_6', A_173) | k3_xboole_0(A_173, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_3378])).
% 4.67/1.91  tff(c_3413, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2315, c_3406])).
% 4.67/1.91  tff(c_3426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2928, c_2, c_3413])).
% 4.67/1.91  tff(c_3427, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1158])).
% 4.67/1.91  tff(c_16, plain, (![A_12, B_13]: (r2_hidden('#skF_2'(A_12, B_13), k3_xboole_0(A_12, B_13)) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.91  tff(c_3455, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3427, c_16])).
% 4.67/1.91  tff(c_3504, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_446, c_3455])).
% 4.67/1.91  tff(c_111, plain, (![B_46, A_47]: (r1_xboole_0(B_46, A_47) | ~r1_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.67/1.91  tff(c_117, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_111])).
% 4.67/1.91  tff(c_1791, plain, (![A_127, C_128, B_129]: (~r1_xboole_0(A_127, C_128) | ~r1_xboole_0(A_127, B_129) | r1_xboole_0(A_127, k2_xboole_0(B_129, C_128)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.67/1.91  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.67/1.91  tff(c_5174, plain, (![B_216, C_217, A_218]: (r1_xboole_0(k2_xboole_0(B_216, C_217), A_218) | ~r1_xboole_0(A_218, C_217) | ~r1_xboole_0(A_218, B_216))), inference(resolution, [status(thm)], [c_1791, c_8])).
% 4.67/1.91  tff(c_44, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.91  tff(c_5200, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_5174, c_44])).
% 4.67/1.91  tff(c_5214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3504, c_117, c_5200])).
% 4.67/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.91  
% 4.67/1.91  Inference rules
% 4.67/1.91  ----------------------
% 4.67/1.91  #Ref     : 0
% 4.67/1.91  #Sup     : 1250
% 4.67/1.91  #Fact    : 0
% 4.67/1.91  #Define  : 0
% 4.67/1.91  #Split   : 4
% 4.67/1.91  #Chain   : 0
% 4.67/1.91  #Close   : 0
% 4.67/1.91  
% 4.67/1.91  Ordering : KBO
% 4.67/1.91  
% 4.67/1.91  Simplification rules
% 4.67/1.91  ----------------------
% 4.67/1.91  #Subsume      : 142
% 4.67/1.91  #Demod        : 936
% 4.67/1.91  #Tautology    : 698
% 4.67/1.91  #SimpNegUnit  : 47
% 4.67/1.91  #BackRed      : 3
% 4.67/1.91  
% 4.67/1.91  #Partial instantiations: 0
% 4.67/1.91  #Strategies tried      : 1
% 4.67/1.91  
% 4.67/1.91  Timing (in seconds)
% 4.67/1.91  ----------------------
% 4.67/1.91  Preprocessing        : 0.31
% 4.67/1.91  Parsing              : 0.17
% 4.67/1.91  CNF conversion       : 0.02
% 4.67/1.91  Main loop            : 0.84
% 5.02/1.91  Inferencing          : 0.25
% 5.02/1.91  Reduction            : 0.36
% 5.02/1.91  Demodulation         : 0.29
% 5.02/1.91  BG Simplification    : 0.03
% 5.02/1.91  Subsumption          : 0.14
% 5.02/1.91  Abstraction          : 0.03
% 5.02/1.91  MUC search           : 0.00
% 5.02/1.91  Cooper               : 0.00
% 5.02/1.91  Total                : 1.18
% 5.02/1.91  Index Insertion      : 0.00
% 5.02/1.91  Index Deletion       : 0.00
% 5.02/1.91  Index Matching       : 0.00
% 5.02/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
