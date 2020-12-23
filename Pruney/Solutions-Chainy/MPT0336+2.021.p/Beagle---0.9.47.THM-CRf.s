%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 6.53s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 135 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 244 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_51,axiom,(
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

tff(f_89,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_2'(A_12,B_13),k3_xboole_0(A_12,B_13))
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_316,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,B_77)
      | ~ r2_hidden(C_78,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_335,plain,(
    ! [C_79] :
      ( ~ r2_hidden(C_79,'#skF_4')
      | ~ r2_hidden(C_79,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_349,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_335])).

tff(c_28,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_489,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_xboole_0(k2_tarski(A_87,C_88),B_89)
      | r2_hidden(C_88,B_89)
      | r2_hidden(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_784,plain,(
    ! [A_98,B_99] :
      ( r1_xboole_0(k1_tarski(A_98),B_99)
      | r2_hidden(A_98,B_99)
      | r2_hidden(A_98,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_489])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_804,plain,(
    ! [B_99,A_98] :
      ( r1_xboole_0(B_99,k1_tarski(A_98))
      | r2_hidden(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_784,c_6])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_226,plain,(
    ! [A_64,B_65,B_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | r1_xboole_0(k3_xboole_0(A_64,B_65),B_66) ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_242,plain,(
    ! [A_3,B_4,B_66] :
      ( ~ r1_xboole_0(A_3,B_4)
      | r1_xboole_0(k3_xboole_0(B_4,A_3),B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_226])).

tff(c_350,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),k3_xboole_0(A_80,B_81))
      | r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_365,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4),k3_xboole_0(B_4,A_3))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_350])).

tff(c_388,plain,(
    ! [A_84,B_85,C_86] : k3_xboole_0(k3_xboole_0(A_84,B_85),C_86) = k3_xboole_0(A_84,k3_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2885,plain,(
    ! [A_143,B_144,C_145,C_146] :
      ( ~ r1_xboole_0(k3_xboole_0(A_143,B_144),C_145)
      | ~ r2_hidden(C_146,k3_xboole_0(A_143,k3_xboole_0(B_144,C_145))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_16])).

tff(c_3031,plain,(
    ! [B_147,B_148,C_149] :
      ( ~ r1_xboole_0(k3_xboole_0(B_147,B_148),C_149)
      | r1_xboole_0(k3_xboole_0(B_148,C_149),B_147) ) ),
    inference(resolution,[status(thm)],[c_365,c_2885])).

tff(c_3112,plain,(
    ! [A_150,B_151,B_152] :
      ( r1_xboole_0(k3_xboole_0(A_150,B_151),B_152)
      | ~ r1_xboole_0(A_150,B_152) ) ),
    inference(resolution,[status(thm)],[c_242,c_3031])).

tff(c_42,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_43,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_127,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_131,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_127])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_166,plain,(
    ! [A_52,B_53,A_7] :
      ( ~ r1_xboole_0(A_52,B_53)
      | r1_xboole_0(A_7,k3_xboole_0(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_204,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | r1_xboole_0(A_7,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_166])).

tff(c_820,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_3188,plain,(
    ~ r1_xboole_0('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3112,c_820])).

tff(c_3195,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_804,c_3188])).

tff(c_3199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_3195])).

tff(c_3200,plain,(
    ! [A_7] : r1_xboole_0(A_7,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_164,plain,(
    ! [B_4,A_3,C_54] :
      ( ~ r1_xboole_0(B_4,A_3)
      | ~ r2_hidden(C_54,k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_150])).

tff(c_207,plain,(
    ! [C_54] :
      ( ~ r1_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(C_54,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_164])).

tff(c_754,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_3205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3200,c_754])).

tff(c_3208,plain,(
    ! [C_153] : ~ r2_hidden(C_153,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_3226,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3208])).

tff(c_53,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_3243,plain,(
    ! [A_154,C_155,B_156] :
      ( ~ r1_xboole_0(A_154,C_155)
      | ~ r1_xboole_0(A_154,B_156)
      | r1_xboole_0(A_154,k2_xboole_0(B_156,C_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5413,plain,(
    ! [B_207,C_208,A_209] :
      ( r1_xboole_0(k2_xboole_0(B_207,C_208),A_209)
      | ~ r1_xboole_0(A_209,C_208)
      | ~ r1_xboole_0(A_209,B_207) ) ),
    inference(resolution,[status(thm)],[c_3243,c_6])).

tff(c_36,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5428,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_5413,c_36])).

tff(c_5442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_56,c_5428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.53/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.70  
% 6.71/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.71/2.70  
% 6.71/2.70  %Foreground sorts:
% 6.71/2.70  
% 6.71/2.70  
% 6.71/2.70  %Background operators:
% 6.71/2.70  
% 6.71/2.70  
% 6.71/2.70  %Foreground operators:
% 6.71/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.71/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.71/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.71/2.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.71/2.70  tff('#skF_5', type, '#skF_5': $i).
% 6.71/2.70  tff('#skF_6', type, '#skF_6': $i).
% 6.71/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.71/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.71/2.70  tff('#skF_3', type, '#skF_3': $i).
% 6.71/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.70  tff('#skF_4', type, '#skF_4': $i).
% 6.71/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.71/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.71/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.71/2.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.71/2.70  
% 6.71/2.72  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.71/2.72  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.71/2.72  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.71/2.72  tff(f_89, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.71/2.72  tff(f_103, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 6.71/2.72  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.71/2.72  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.71/2.72  tff(f_67, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.71/2.72  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.71/2.72  tff(f_87, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.71/2.72  tff(c_14, plain, (![A_12, B_13]: (r2_hidden('#skF_2'(A_12, B_13), k3_xboole_0(A_12, B_13)) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.71/2.72  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.71/2.72  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.71/2.72  tff(c_316, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, B_77) | ~r2_hidden(C_78, A_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.71/2.72  tff(c_335, plain, (![C_79]: (~r2_hidden(C_79, '#skF_4') | ~r2_hidden(C_79, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_316])).
% 6.71/2.72  tff(c_349, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_335])).
% 6.71/2.72  tff(c_28, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.71/2.72  tff(c_489, plain, (![A_87, C_88, B_89]: (r1_xboole_0(k2_tarski(A_87, C_88), B_89) | r2_hidden(C_88, B_89) | r2_hidden(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.71/2.72  tff(c_784, plain, (![A_98, B_99]: (r1_xboole_0(k1_tarski(A_98), B_99) | r2_hidden(A_98, B_99) | r2_hidden(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_28, c_489])).
% 6.71/2.72  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.71/2.72  tff(c_804, plain, (![B_99, A_98]: (r1_xboole_0(B_99, k1_tarski(A_98)) | r2_hidden(A_98, B_99))), inference(resolution, [status(thm)], [c_784, c_6])).
% 6.71/2.72  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.71/2.72  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.71/2.72  tff(c_150, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.71/2.72  tff(c_226, plain, (![A_64, B_65, B_66]: (~r1_xboole_0(A_64, B_65) | r1_xboole_0(k3_xboole_0(A_64, B_65), B_66))), inference(resolution, [status(thm)], [c_12, c_150])).
% 6.71/2.72  tff(c_242, plain, (![A_3, B_4, B_66]: (~r1_xboole_0(A_3, B_4) | r1_xboole_0(k3_xboole_0(B_4, A_3), B_66))), inference(superposition, [status(thm), theory('equality')], [c_4, c_226])).
% 6.71/2.72  tff(c_350, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), k3_xboole_0(A_80, B_81)) | r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.71/2.72  tff(c_365, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4), k3_xboole_0(B_4, A_3)) | r1_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_350])).
% 6.71/2.72  tff(c_388, plain, (![A_84, B_85, C_86]: (k3_xboole_0(k3_xboole_0(A_84, B_85), C_86)=k3_xboole_0(A_84, k3_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.71/2.72  tff(c_16, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.71/2.72  tff(c_2885, plain, (![A_143, B_144, C_145, C_146]: (~r1_xboole_0(k3_xboole_0(A_143, B_144), C_145) | ~r2_hidden(C_146, k3_xboole_0(A_143, k3_xboole_0(B_144, C_145))))), inference(superposition, [status(thm), theory('equality')], [c_388, c_16])).
% 6.71/2.72  tff(c_3031, plain, (![B_147, B_148, C_149]: (~r1_xboole_0(k3_xboole_0(B_147, B_148), C_149) | r1_xboole_0(k3_xboole_0(B_148, C_149), B_147))), inference(resolution, [status(thm)], [c_365, c_2885])).
% 6.71/2.72  tff(c_3112, plain, (![A_150, B_151, B_152]: (r1_xboole_0(k3_xboole_0(A_150, B_151), B_152) | ~r1_xboole_0(A_150, B_152))), inference(resolution, [status(thm)], [c_242, c_3031])).
% 6.71/2.72  tff(c_42, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.71/2.72  tff(c_43, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_42])).
% 6.71/2.72  tff(c_127, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.71/2.72  tff(c_131, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_43, c_127])).
% 6.71/2.72  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.71/2.72  tff(c_166, plain, (![A_52, B_53, A_7]: (~r1_xboole_0(A_52, B_53) | r1_xboole_0(A_7, k3_xboole_0(A_52, B_53)))), inference(resolution, [status(thm)], [c_10, c_150])).
% 6.71/2.72  tff(c_204, plain, (![A_7]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | r1_xboole_0(A_7, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_166])).
% 6.71/2.72  tff(c_820, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_204])).
% 6.71/2.72  tff(c_3188, plain, (~r1_xboole_0('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_3112, c_820])).
% 6.71/2.72  tff(c_3195, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_804, c_3188])).
% 6.71/2.72  tff(c_3199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_349, c_3195])).
% 6.71/2.72  tff(c_3200, plain, (![A_7]: (r1_xboole_0(A_7, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_204])).
% 6.71/2.72  tff(c_164, plain, (![B_4, A_3, C_54]: (~r1_xboole_0(B_4, A_3) | ~r2_hidden(C_54, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_150])).
% 6.71/2.72  tff(c_207, plain, (![C_54]: (~r1_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(C_54, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_164])).
% 6.71/2.72  tff(c_754, plain, (~r1_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_207])).
% 6.71/2.72  tff(c_3205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3200, c_754])).
% 6.71/2.72  tff(c_3208, plain, (![C_153]: (~r2_hidden(C_153, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_207])).
% 6.71/2.72  tff(c_3226, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_3208])).
% 6.71/2.72  tff(c_53, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.71/2.72  tff(c_56, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_53])).
% 6.71/2.72  tff(c_3243, plain, (![A_154, C_155, B_156]: (~r1_xboole_0(A_154, C_155) | ~r1_xboole_0(A_154, B_156) | r1_xboole_0(A_154, k2_xboole_0(B_156, C_155)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.71/2.72  tff(c_5413, plain, (![B_207, C_208, A_209]: (r1_xboole_0(k2_xboole_0(B_207, C_208), A_209) | ~r1_xboole_0(A_209, C_208) | ~r1_xboole_0(A_209, B_207))), inference(resolution, [status(thm)], [c_3243, c_6])).
% 6.71/2.72  tff(c_36, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.71/2.72  tff(c_5428, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_5413, c_36])).
% 6.71/2.72  tff(c_5442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3226, c_56, c_5428])).
% 6.71/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.72  
% 6.71/2.72  Inference rules
% 6.71/2.72  ----------------------
% 6.71/2.72  #Ref     : 0
% 6.71/2.72  #Sup     : 1478
% 6.71/2.72  #Fact    : 0
% 6.71/2.72  #Define  : 0
% 6.71/2.72  #Split   : 3
% 6.71/2.72  #Chain   : 0
% 6.71/2.72  #Close   : 0
% 6.71/2.72  
% 6.71/2.72  Ordering : KBO
% 6.71/2.72  
% 6.71/2.72  Simplification rules
% 6.71/2.72  ----------------------
% 6.71/2.72  #Subsume      : 247
% 6.71/2.72  #Demod        : 725
% 6.71/2.72  #Tautology    : 265
% 6.71/2.72  #SimpNegUnit  : 3
% 6.71/2.72  #BackRed      : 1
% 6.71/2.72  
% 6.71/2.72  #Partial instantiations: 0
% 6.71/2.72  #Strategies tried      : 1
% 6.71/2.72  
% 6.71/2.72  Timing (in seconds)
% 6.71/2.72  ----------------------
% 6.71/2.72  Preprocessing        : 0.36
% 6.71/2.72  Parsing              : 0.21
% 6.71/2.72  CNF conversion       : 0.03
% 6.71/2.72  Main loop            : 1.53
% 6.71/2.72  Inferencing          : 0.34
% 6.71/2.72  Reduction            : 0.88
% 6.71/2.72  Demodulation         : 0.80
% 6.71/2.72  BG Simplification    : 0.05
% 6.71/2.72  Subsumption          : 0.18
% 6.71/2.72  Abstraction          : 0.07
% 6.71/2.72  MUC search           : 0.00
% 6.71/2.72  Cooper               : 0.00
% 6.71/2.72  Total                : 1.93
% 6.71/2.72  Index Insertion      : 0.00
% 6.71/2.72  Index Deletion       : 0.00
% 6.71/2.72  Index Matching       : 0.00
% 6.71/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
