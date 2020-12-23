%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:00 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 251 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  121 ( 543 expanded)
%              Number of equality atoms :   60 ( 265 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_131,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [C_32] :
      ( C_32 = '#skF_5'
      | ~ r2_hidden(C_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_143,plain,(
    ! [B_64] :
      ( '#skF_1'('#skF_4',B_64) = '#skF_5'
      | r1_tarski('#skF_4',B_64) ) ),
    inference(resolution,[status(thm)],[c_131,c_54])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [B_11] :
      ( k1_xboole_0 = '#skF_4'
      | '#skF_1'('#skF_4',k4_xboole_0(B_11,'#skF_4')) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_143,c_16])).

tff(c_151,plain,(
    ! [B_65] : '#skF_1'('#skF_4',k4_xboole_0(B_65,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_147])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_5','#skF_4')
      | r1_tarski('#skF_4',k4_xboole_0(B_65,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_6])).

tff(c_177,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_142,plain,(
    ! [B_63] :
      ( '#skF_1'('#skF_4',B_63) = '#skF_5'
      | r1_tarski('#skF_4',B_63) ) ),
    inference(resolution,[status(thm)],[c_131,c_54])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_382,plain,(
    ! [A_107,B_108] :
      ( k1_tarski(A_107) = B_108
      | ~ r1_tarski(B_108,k1_tarski(A_107))
      | ~ r2_hidden(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_52,c_164])).

tff(c_395,plain,(
    ! [A_107] :
      ( k1_tarski(A_107) = '#skF_4'
      | ~ r2_hidden(A_107,'#skF_4')
      | '#skF_1'('#skF_4',k1_tarski(A_107)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_142,c_382])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,B_50)
      | ~ r1_tarski(k1_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ! [A_49] : r2_hidden(A_49,k1_tarski(A_49)) ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_150,plain,(
    ! [B_11] : '#skF_1'('#skF_4',k4_xboole_0(B_11,'#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_147])).

tff(c_192,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [A_1,B_2,B_72] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_72)
      | ~ r1_tarski(A_1,B_72)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_42,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_416,plain,(
    ! [E_113,C_114,B_115,A_116] :
      ( E_113 = C_114
      | E_113 = B_115
      | E_113 = A_116
      | ~ r2_hidden(E_113,k1_enumset1(A_116,B_115,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_494,plain,(
    ! [E_122,B_123,A_124] :
      ( E_122 = B_123
      | E_122 = A_124
      | E_122 = A_124
      | ~ r2_hidden(E_122,k2_tarski(A_124,B_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_416])).

tff(c_586,plain,(
    ! [E_130,A_131] :
      ( E_130 = A_131
      | E_130 = A_131
      | E_130 = A_131
      | ~ r2_hidden(E_130,k1_tarski(A_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_494])).

tff(c_767,plain,(
    ! [A_149,A_150,B_151] :
      ( A_149 = '#skF_1'(A_150,B_151)
      | ~ r1_tarski(A_150,k1_tarski(A_149))
      | r1_tarski(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_210,c_586])).

tff(c_951,plain,(
    ! [A_173,B_174] :
      ( A_173 = '#skF_1'('#skF_4',B_174)
      | r1_tarski('#skF_4',B_174)
      | '#skF_1'('#skF_4',k1_tarski(A_173)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_142,c_767])).

tff(c_209,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_5',B_72)
      | ~ r1_tarski('#skF_4',B_72) ) ),
    inference(resolution,[status(thm)],[c_177,c_192])).

tff(c_547,plain,(
    ! [B_126,A_127] :
      ( B_126 = '#skF_5'
      | A_127 = '#skF_5'
      | ~ r1_tarski('#skF_4',k2_tarski(A_127,B_126)) ) ),
    inference(resolution,[status(thm)],[c_209,c_494])).

tff(c_553,plain,(
    ! [A_19] :
      ( A_19 = '#skF_5'
      | A_19 = '#skF_5'
      | ~ r1_tarski('#skF_4',k1_tarski(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_547])).

tff(c_4027,plain,(
    ! [A_5008,A_5009] :
      ( A_5008 = '#skF_5'
      | A_5009 = '#skF_1'('#skF_4',k1_tarski(A_5008))
      | '#skF_1'('#skF_4',k1_tarski(A_5009)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_951,c_553])).

tff(c_5177,plain,(
    ! [A_5008,B_11] :
      ( '#skF_1'('#skF_4',k1_tarski(A_5008)) = '#skF_5'
      | A_5008 = '#skF_5'
      | '#skF_1'('#skF_4',k1_tarski('#skF_1'('#skF_4',k4_xboole_0(B_11,'#skF_4')))) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4027,c_150])).

tff(c_5796,plain,(
    ! [A_5008] :
      ( '#skF_1'('#skF_4',k1_tarski(A_5008)) = '#skF_5'
      | A_5008 = '#skF_5'
      | '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_5177])).

tff(c_5812,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5796])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5856,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5812,c_4])).

tff(c_5980,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5856])).

tff(c_172,plain,(
    ! [A_29,B_30] :
      ( k1_tarski(A_29) = B_30
      | ~ r1_tarski(B_30,k1_tarski(A_29))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_52,c_164])).

tff(c_6006,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5980,c_172])).

tff(c_6025,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_6006])).

tff(c_6027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6025])).

tff(c_6029,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5796])).

tff(c_6064,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_6029])).

tff(c_6074,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_6064])).

tff(c_6076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6074])).

tff(c_6097,plain,(
    ! [B_7867] : r1_tarski('#skF_4',k4_xboole_0(B_7867,'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_6102,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6097,c_16])).

tff(c_6107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.99/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.18  
% 5.99/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.18  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.99/2.18  
% 5.99/2.18  %Foreground sorts:
% 5.99/2.18  
% 5.99/2.18  
% 5.99/2.18  %Background operators:
% 5.99/2.18  
% 5.99/2.18  
% 5.99/2.18  %Foreground operators:
% 5.99/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.99/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.99/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.99/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.99/2.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.99/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.99/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.99/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.99/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.99/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.99/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.99/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.99/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.99/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.99/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.99/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.99/2.18  
% 5.99/2.20  tff(f_86, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 5.99/2.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.99/2.20  tff(f_44, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 5.99/2.20  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.99/2.20  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.99/2.20  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.99/2.20  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.99/2.20  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.99/2.20  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.99/2.20  tff(c_58, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.99/2.20  tff(c_131, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.99/2.20  tff(c_54, plain, (![C_32]: (C_32='#skF_5' | ~r2_hidden(C_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.99/2.20  tff(c_143, plain, (![B_64]: ('#skF_1'('#skF_4', B_64)='#skF_5' | r1_tarski('#skF_4', B_64))), inference(resolution, [status(thm)], [c_131, c_54])).
% 5.99/2.20  tff(c_16, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k4_xboole_0(B_11, A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.99/2.20  tff(c_147, plain, (![B_11]: (k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k4_xboole_0(B_11, '#skF_4'))='#skF_5')), inference(resolution, [status(thm)], [c_143, c_16])).
% 5.99/2.20  tff(c_151, plain, (![B_65]: ('#skF_1'('#skF_4', k4_xboole_0(B_65, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_147])).
% 5.99/2.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.99/2.20  tff(c_156, plain, (![B_65]: (r2_hidden('#skF_5', '#skF_4') | r1_tarski('#skF_4', k4_xboole_0(B_65, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_151, c_6])).
% 5.99/2.20  tff(c_177, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_156])).
% 5.99/2.20  tff(c_142, plain, (![B_63]: ('#skF_1'('#skF_4', B_63)='#skF_5' | r1_tarski('#skF_4', B_63))), inference(resolution, [status(thm)], [c_131, c_54])).
% 5.99/2.20  tff(c_52, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.99/2.20  tff(c_164, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.99/2.20  tff(c_382, plain, (![A_107, B_108]: (k1_tarski(A_107)=B_108 | ~r1_tarski(B_108, k1_tarski(A_107)) | ~r2_hidden(A_107, B_108))), inference(resolution, [status(thm)], [c_52, c_164])).
% 5.99/2.20  tff(c_395, plain, (![A_107]: (k1_tarski(A_107)='#skF_4' | ~r2_hidden(A_107, '#skF_4') | '#skF_1'('#skF_4', k1_tarski(A_107))='#skF_5')), inference(resolution, [status(thm)], [c_142, c_382])).
% 5.99/2.20  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.99/2.20  tff(c_81, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50) | ~r1_tarski(k1_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.99/2.20  tff(c_90, plain, (![A_49]: (r2_hidden(A_49, k1_tarski(A_49)))), inference(resolution, [status(thm)], [c_12, c_81])).
% 5.99/2.20  tff(c_150, plain, (![B_11]: ('#skF_1'('#skF_4', k4_xboole_0(B_11, '#skF_4'))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_147])).
% 5.99/2.20  tff(c_192, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.99/2.20  tff(c_210, plain, (![A_1, B_2, B_72]: (r2_hidden('#skF_1'(A_1, B_2), B_72) | ~r1_tarski(A_1, B_72) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_192])).
% 5.99/2.20  tff(c_42, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.99/2.20  tff(c_44, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.99/2.20  tff(c_416, plain, (![E_113, C_114, B_115, A_116]: (E_113=C_114 | E_113=B_115 | E_113=A_116 | ~r2_hidden(E_113, k1_enumset1(A_116, B_115, C_114)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.99/2.20  tff(c_494, plain, (![E_122, B_123, A_124]: (E_122=B_123 | E_122=A_124 | E_122=A_124 | ~r2_hidden(E_122, k2_tarski(A_124, B_123)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_416])).
% 5.99/2.20  tff(c_586, plain, (![E_130, A_131]: (E_130=A_131 | E_130=A_131 | E_130=A_131 | ~r2_hidden(E_130, k1_tarski(A_131)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_494])).
% 5.99/2.20  tff(c_767, plain, (![A_149, A_150, B_151]: (A_149='#skF_1'(A_150, B_151) | ~r1_tarski(A_150, k1_tarski(A_149)) | r1_tarski(A_150, B_151))), inference(resolution, [status(thm)], [c_210, c_586])).
% 5.99/2.20  tff(c_951, plain, (![A_173, B_174]: (A_173='#skF_1'('#skF_4', B_174) | r1_tarski('#skF_4', B_174) | '#skF_1'('#skF_4', k1_tarski(A_173))='#skF_5')), inference(resolution, [status(thm)], [c_142, c_767])).
% 5.99/2.20  tff(c_209, plain, (![B_72]: (r2_hidden('#skF_5', B_72) | ~r1_tarski('#skF_4', B_72))), inference(resolution, [status(thm)], [c_177, c_192])).
% 5.99/2.20  tff(c_547, plain, (![B_126, A_127]: (B_126='#skF_5' | A_127='#skF_5' | ~r1_tarski('#skF_4', k2_tarski(A_127, B_126)))), inference(resolution, [status(thm)], [c_209, c_494])).
% 5.99/2.20  tff(c_553, plain, (![A_19]: (A_19='#skF_5' | A_19='#skF_5' | ~r1_tarski('#skF_4', k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_547])).
% 5.99/2.20  tff(c_4027, plain, (![A_5008, A_5009]: (A_5008='#skF_5' | A_5009='#skF_1'('#skF_4', k1_tarski(A_5008)) | '#skF_1'('#skF_4', k1_tarski(A_5009))='#skF_5')), inference(resolution, [status(thm)], [c_951, c_553])).
% 5.99/2.20  tff(c_5177, plain, (![A_5008, B_11]: ('#skF_1'('#skF_4', k1_tarski(A_5008))='#skF_5' | A_5008='#skF_5' | '#skF_1'('#skF_4', k1_tarski('#skF_1'('#skF_4', k4_xboole_0(B_11, '#skF_4'))))='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4027, c_150])).
% 5.99/2.20  tff(c_5796, plain, (![A_5008]: ('#skF_1'('#skF_4', k1_tarski(A_5008))='#skF_5' | A_5008='#skF_5' | '#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_5177])).
% 5.99/2.20  tff(c_5812, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(splitLeft, [status(thm)], [c_5796])).
% 5.99/2.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.99/2.20  tff(c_5856, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5812, c_4])).
% 5.99/2.20  tff(c_5980, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5856])).
% 5.99/2.20  tff(c_172, plain, (![A_29, B_30]: (k1_tarski(A_29)=B_30 | ~r1_tarski(B_30, k1_tarski(A_29)) | ~r2_hidden(A_29, B_30))), inference(resolution, [status(thm)], [c_52, c_164])).
% 5.99/2.20  tff(c_6006, plain, (k1_tarski('#skF_5')='#skF_4' | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5980, c_172])).
% 5.99/2.20  tff(c_6025, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_6006])).
% 5.99/2.20  tff(c_6027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_6025])).
% 5.99/2.20  tff(c_6029, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))!='#skF_5'), inference(splitRight, [status(thm)], [c_5796])).
% 5.99/2.20  tff(c_6064, plain, (k1_tarski('#skF_5')='#skF_4' | ~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_395, c_6029])).
% 5.99/2.20  tff(c_6074, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_6064])).
% 5.99/2.20  tff(c_6076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_6074])).
% 5.99/2.20  tff(c_6097, plain, (![B_7867]: (r1_tarski('#skF_4', k4_xboole_0(B_7867, '#skF_4')))), inference(splitRight, [status(thm)], [c_156])).
% 5.99/2.20  tff(c_6102, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6097, c_16])).
% 5.99/2.20  tff(c_6107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6102])).
% 5.99/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.20  
% 5.99/2.20  Inference rules
% 5.99/2.20  ----------------------
% 5.99/2.20  #Ref     : 0
% 5.99/2.20  #Sup     : 1113
% 5.99/2.20  #Fact    : 2
% 5.99/2.20  #Define  : 0
% 5.99/2.20  #Split   : 3
% 5.99/2.20  #Chain   : 0
% 5.99/2.20  #Close   : 0
% 5.99/2.20  
% 5.99/2.20  Ordering : KBO
% 5.99/2.20  
% 5.99/2.20  Simplification rules
% 5.99/2.20  ----------------------
% 5.99/2.20  #Subsume      : 447
% 5.99/2.20  #Demod        : 72
% 5.99/2.20  #Tautology    : 122
% 5.99/2.20  #SimpNegUnit  : 35
% 5.99/2.20  #BackRed      : 0
% 5.99/2.20  
% 5.99/2.20  #Partial instantiations: 3444
% 5.99/2.20  #Strategies tried      : 1
% 5.99/2.20  
% 5.99/2.20  Timing (in seconds)
% 5.99/2.20  ----------------------
% 5.99/2.20  Preprocessing        : 0.33
% 5.99/2.20  Parsing              : 0.17
% 5.99/2.20  CNF conversion       : 0.03
% 5.99/2.20  Main loop            : 1.10
% 5.99/2.20  Inferencing          : 0.41
% 5.99/2.20  Reduction            : 0.30
% 5.99/2.20  Demodulation         : 0.20
% 5.99/2.21  BG Simplification    : 0.04
% 5.99/2.21  Subsumption          : 0.30
% 5.99/2.21  Abstraction          : 0.04
% 5.99/2.21  MUC search           : 0.00
% 5.99/2.21  Cooper               : 0.00
% 5.99/2.21  Total                : 1.47
% 5.99/2.21  Index Insertion      : 0.00
% 5.99/2.21  Index Deletion       : 0.00
% 5.99/2.21  Index Matching       : 0.00
% 5.99/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
