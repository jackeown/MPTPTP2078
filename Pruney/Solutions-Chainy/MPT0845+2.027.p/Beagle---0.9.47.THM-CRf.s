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
% DateTime   : Thu Dec  3 10:08:48 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 127 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 294 expanded)
%              Number of equality atoms :   18 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1004,plain,(
    ! [A_177,B_178,C_179] :
      ( r2_hidden('#skF_1'(A_177,B_178,C_179),A_177)
      | r2_hidden('#skF_2'(A_177,B_178,C_179),C_179)
      | k3_xboole_0(A_177,B_178) = C_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1055,plain,(
    ! [A_177,B_178] :
      ( r2_hidden('#skF_2'(A_177,B_178,A_177),A_177)
      | k3_xboole_0(A_177,B_178) = A_177 ) ),
    inference(resolution,[status(thm)],[c_1004,c_14])).

tff(c_1065,plain,(
    ! [A_180,B_181] :
      ( r2_hidden('#skF_2'(A_180,B_181,A_180),A_180)
      | k3_xboole_0(A_180,B_181) = A_180 ) ),
    inference(resolution,[status(thm)],[c_1004,c_14])).

tff(c_30,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_159,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [C_85,A_16] :
      ( ~ r2_hidden(C_85,k1_xboole_0)
      | ~ r2_hidden(C_85,A_16) ) ),
    inference(resolution,[status(thm)],[c_30,c_159])).

tff(c_1099,plain,(
    ! [B_183,A_184] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_183,k1_xboole_0),A_184)
      | k3_xboole_0(k1_xboole_0,B_183) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1065,c_165])).

tff(c_1116,plain,(
    ! [B_178] : k3_xboole_0(k1_xboole_0,B_178) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1055,c_1099])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_641,plain,(
    ! [A_157,B_158,C_159] :
      ( r2_hidden('#skF_1'(A_157,B_158,C_159),B_158)
      | r2_hidden('#skF_2'(A_157,B_158,C_159),C_159)
      | k3_xboole_0(A_157,B_158) = C_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_686,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_2'(A_157,B_158,B_158),B_158)
      | k3_xboole_0(A_157,B_158) = B_158 ) ),
    inference(resolution,[status(thm)],[c_641,c_14])).

tff(c_788,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_2'(A_166,B_167,B_167),B_167)
      | k3_xboole_0(A_166,B_167) = B_167 ) ),
    inference(resolution,[status(thm)],[c_641,c_14])).

tff(c_822,plain,(
    ! [A_169,A_170] :
      ( ~ r2_hidden('#skF_2'(A_169,k1_xboole_0,k1_xboole_0),A_170)
      | k3_xboole_0(A_169,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_788,c_165])).

tff(c_833,plain,(
    ! [A_157] : k3_xboole_0(A_157,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_686,c_822])).

tff(c_131,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_4'(A_75,B_76),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_145,plain,(
    ! [A_75,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_75,k3_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden(A_75,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_46,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_4'(A_44,B_45),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_99,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_3'(A_71,B_72),A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,(
    ! [A_1,B_2,B_72] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_1,B_2),B_72),A_1)
      | r1_xboole_0(k3_xboole_0(A_1,B_2),B_72) ) ),
    inference(resolution,[status(thm)],[c_99,c_6])).

tff(c_267,plain,(
    ! [A_108,B_109,B_110] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_108,B_109),B_110),A_108)
      | r1_xboole_0(k3_xboole_0(A_108,B_109),B_110) ) ),
    inference(resolution,[status(thm)],[c_99,c_6])).

tff(c_563,plain,(
    ! [B_148,B_149,A_150] :
      ( ~ r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0,B_148),B_149),A_150)
      | r1_xboole_0(k3_xboole_0(k1_xboole_0,B_148),B_149) ) ),
    inference(resolution,[status(thm)],[c_267,c_165])).

tff(c_605,plain,(
    ! [B_151,B_152] : r1_xboole_0(k3_xboole_0(k1_xboole_0,B_151),B_152) ),
    inference(resolution,[status(thm)],[c_112,c_563])).

tff(c_24,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_697,plain,(
    ! [C_160,B_161,B_162] :
      ( ~ r2_hidden(C_160,B_161)
      | ~ r2_hidden(C_160,k3_xboole_0(k1_xboole_0,B_162)) ) ),
    inference(resolution,[status(thm)],[c_605,c_24])).

tff(c_731,plain,(
    ! [A_44,B_45,B_162] :
      ( ~ r2_hidden('#skF_4'(A_44,B_45),k3_xboole_0(k1_xboole_0,B_162))
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_46,c_697])).

tff(c_1196,plain,(
    ! [A_186,B_187] :
      ( ~ r2_hidden('#skF_4'(A_186,B_187),k1_xboole_0)
      | ~ r2_hidden(A_186,B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_731])).

tff(c_1204,plain,(
    ! [A_75,A_1] : ~ r2_hidden(A_75,k3_xboole_0(A_1,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_145,c_1196])).

tff(c_1219,plain,(
    ! [A_188] : ~ r2_hidden(A_188,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_1204])).

tff(c_1227,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k3_xboole_0(k1_xboole_0,B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_1219])).

tff(c_1279,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_1227])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_181,plain,(
    ! [D_88,A_89,B_90] :
      ( ~ r2_hidden(D_88,'#skF_4'(A_89,B_90))
      | ~ r2_hidden(D_88,B_90)
      | ~ r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1803,plain,(
    ! [A_241,A_242,B_243] :
      ( ~ r2_hidden('#skF_3'(A_241,'#skF_4'(A_242,B_243)),B_243)
      | ~ r2_hidden(A_242,B_243)
      | r1_xboole_0(A_241,'#skF_4'(A_242,B_243)) ) ),
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_1824,plain,(
    ! [A_244,A_245] :
      ( ~ r2_hidden(A_244,A_245)
      | r1_xboole_0(A_245,'#skF_4'(A_244,A_245)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1803])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1831,plain,(
    ! [A_246,A_247] :
      ( r1_xboole_0('#skF_4'(A_246,A_247),A_247)
      | ~ r2_hidden(A_246,A_247) ) ),
    inference(resolution,[status(thm)],[c_1824,c_22])).

tff(c_50,plain,(
    ! [B_54] :
      ( ~ r1_xboole_0(B_54,'#skF_5')
      | ~ r2_hidden(B_54,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_146,plain,(
    ! [A_75] :
      ( ~ r1_xboole_0('#skF_4'(A_75,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_75,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_131,c_50])).

tff(c_1843,plain,(
    ! [A_248] : ~ r2_hidden(A_248,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1831,c_146])).

tff(c_1871,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1279,c_1843])).

tff(c_1941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:55:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.56  
% 3.64/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.56  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.64/1.56  
% 3.64/1.56  %Foreground sorts:
% 3.64/1.56  
% 3.64/1.56  
% 3.64/1.56  %Background operators:
% 3.64/1.56  
% 3.64/1.56  
% 3.64/1.56  %Foreground operators:
% 3.64/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.64/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.64/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.64/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.64/1.56  
% 3.64/1.58  tff(f_98, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.64/1.58  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.64/1.58  tff(f_60, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.64/1.58  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.64/1.58  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.64/1.58  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.64/1.58  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.58  tff(c_1004, plain, (![A_177, B_178, C_179]: (r2_hidden('#skF_1'(A_177, B_178, C_179), A_177) | r2_hidden('#skF_2'(A_177, B_178, C_179), C_179) | k3_xboole_0(A_177, B_178)=C_179)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.58  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.58  tff(c_1055, plain, (![A_177, B_178]: (r2_hidden('#skF_2'(A_177, B_178, A_177), A_177) | k3_xboole_0(A_177, B_178)=A_177)), inference(resolution, [status(thm)], [c_1004, c_14])).
% 3.64/1.58  tff(c_1065, plain, (![A_180, B_181]: (r2_hidden('#skF_2'(A_180, B_181, A_180), A_180) | k3_xboole_0(A_180, B_181)=A_180)), inference(resolution, [status(thm)], [c_1004, c_14])).
% 3.64/1.58  tff(c_30, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.64/1.58  tff(c_159, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.58  tff(c_165, plain, (![C_85, A_16]: (~r2_hidden(C_85, k1_xboole_0) | ~r2_hidden(C_85, A_16))), inference(resolution, [status(thm)], [c_30, c_159])).
% 3.64/1.58  tff(c_1099, plain, (![B_183, A_184]: (~r2_hidden('#skF_2'(k1_xboole_0, B_183, k1_xboole_0), A_184) | k3_xboole_0(k1_xboole_0, B_183)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1065, c_165])).
% 3.64/1.58  tff(c_1116, plain, (![B_178]: (k3_xboole_0(k1_xboole_0, B_178)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1055, c_1099])).
% 3.64/1.58  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.58  tff(c_641, plain, (![A_157, B_158, C_159]: (r2_hidden('#skF_1'(A_157, B_158, C_159), B_158) | r2_hidden('#skF_2'(A_157, B_158, C_159), C_159) | k3_xboole_0(A_157, B_158)=C_159)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.58  tff(c_686, plain, (![A_157, B_158]: (r2_hidden('#skF_2'(A_157, B_158, B_158), B_158) | k3_xboole_0(A_157, B_158)=B_158)), inference(resolution, [status(thm)], [c_641, c_14])).
% 3.64/1.58  tff(c_788, plain, (![A_166, B_167]: (r2_hidden('#skF_2'(A_166, B_167, B_167), B_167) | k3_xboole_0(A_166, B_167)=B_167)), inference(resolution, [status(thm)], [c_641, c_14])).
% 3.64/1.58  tff(c_822, plain, (![A_169, A_170]: (~r2_hidden('#skF_2'(A_169, k1_xboole_0, k1_xboole_0), A_170) | k3_xboole_0(A_169, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_788, c_165])).
% 3.64/1.58  tff(c_833, plain, (![A_157]: (k3_xboole_0(A_157, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_686, c_822])).
% 3.64/1.58  tff(c_131, plain, (![A_75, B_76]: (r2_hidden('#skF_4'(A_75, B_76), B_76) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.58  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.58  tff(c_145, plain, (![A_75, A_1, B_2]: (r2_hidden('#skF_4'(A_75, k3_xboole_0(A_1, B_2)), B_2) | ~r2_hidden(A_75, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_131, c_4])).
% 3.64/1.58  tff(c_46, plain, (![A_44, B_45]: (r2_hidden('#skF_4'(A_44, B_45), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.58  tff(c_99, plain, (![A_71, B_72]: (r2_hidden('#skF_3'(A_71, B_72), A_71) | r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.58  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.64/1.58  tff(c_112, plain, (![A_1, B_2, B_72]: (r2_hidden('#skF_3'(k3_xboole_0(A_1, B_2), B_72), A_1) | r1_xboole_0(k3_xboole_0(A_1, B_2), B_72))), inference(resolution, [status(thm)], [c_99, c_6])).
% 3.64/1.58  tff(c_267, plain, (![A_108, B_109, B_110]: (r2_hidden('#skF_3'(k3_xboole_0(A_108, B_109), B_110), A_108) | r1_xboole_0(k3_xboole_0(A_108, B_109), B_110))), inference(resolution, [status(thm)], [c_99, c_6])).
% 3.64/1.58  tff(c_563, plain, (![B_148, B_149, A_150]: (~r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0, B_148), B_149), A_150) | r1_xboole_0(k3_xboole_0(k1_xboole_0, B_148), B_149))), inference(resolution, [status(thm)], [c_267, c_165])).
% 3.64/1.58  tff(c_605, plain, (![B_151, B_152]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, B_151), B_152))), inference(resolution, [status(thm)], [c_112, c_563])).
% 3.64/1.58  tff(c_24, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, B_12) | ~r2_hidden(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.58  tff(c_697, plain, (![C_160, B_161, B_162]: (~r2_hidden(C_160, B_161) | ~r2_hidden(C_160, k3_xboole_0(k1_xboole_0, B_162)))), inference(resolution, [status(thm)], [c_605, c_24])).
% 3.64/1.58  tff(c_731, plain, (![A_44, B_45, B_162]: (~r2_hidden('#skF_4'(A_44, B_45), k3_xboole_0(k1_xboole_0, B_162)) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_46, c_697])).
% 3.64/1.58  tff(c_1196, plain, (![A_186, B_187]: (~r2_hidden('#skF_4'(A_186, B_187), k1_xboole_0) | ~r2_hidden(A_186, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_731])).
% 3.64/1.58  tff(c_1204, plain, (![A_75, A_1]: (~r2_hidden(A_75, k3_xboole_0(A_1, k1_xboole_0)))), inference(resolution, [status(thm)], [c_145, c_1196])).
% 3.64/1.58  tff(c_1219, plain, (![A_188]: (~r2_hidden(A_188, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_1204])).
% 3.64/1.58  tff(c_1227, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k3_xboole_0(k1_xboole_0, B_2)=C_3)), inference(resolution, [status(thm)], [c_18, c_1219])).
% 3.64/1.58  tff(c_1279, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_1227])).
% 3.64/1.58  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.58  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.64/1.58  tff(c_181, plain, (![D_88, A_89, B_90]: (~r2_hidden(D_88, '#skF_4'(A_89, B_90)) | ~r2_hidden(D_88, B_90) | ~r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.58  tff(c_1803, plain, (![A_241, A_242, B_243]: (~r2_hidden('#skF_3'(A_241, '#skF_4'(A_242, B_243)), B_243) | ~r2_hidden(A_242, B_243) | r1_xboole_0(A_241, '#skF_4'(A_242, B_243)))), inference(resolution, [status(thm)], [c_26, c_181])).
% 3.64/1.58  tff(c_1824, plain, (![A_244, A_245]: (~r2_hidden(A_244, A_245) | r1_xboole_0(A_245, '#skF_4'(A_244, A_245)))), inference(resolution, [status(thm)], [c_28, c_1803])).
% 3.64/1.58  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.64/1.58  tff(c_1831, plain, (![A_246, A_247]: (r1_xboole_0('#skF_4'(A_246, A_247), A_247) | ~r2_hidden(A_246, A_247))), inference(resolution, [status(thm)], [c_1824, c_22])).
% 3.64/1.58  tff(c_50, plain, (![B_54]: (~r1_xboole_0(B_54, '#skF_5') | ~r2_hidden(B_54, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.58  tff(c_146, plain, (![A_75]: (~r1_xboole_0('#skF_4'(A_75, '#skF_5'), '#skF_5') | ~r2_hidden(A_75, '#skF_5'))), inference(resolution, [status(thm)], [c_131, c_50])).
% 3.64/1.58  tff(c_1843, plain, (![A_248]: (~r2_hidden(A_248, '#skF_5'))), inference(resolution, [status(thm)], [c_1831, c_146])).
% 3.64/1.58  tff(c_1871, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1279, c_1843])).
% 3.64/1.58  tff(c_1941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1871])).
% 3.64/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.58  
% 3.64/1.58  Inference rules
% 3.64/1.58  ----------------------
% 3.64/1.58  #Ref     : 0
% 3.64/1.58  #Sup     : 381
% 3.64/1.58  #Fact    : 0
% 3.64/1.58  #Define  : 0
% 3.64/1.58  #Split   : 0
% 3.64/1.58  #Chain   : 0
% 3.64/1.58  #Close   : 0
% 3.64/1.58  
% 3.64/1.58  Ordering : KBO
% 3.64/1.58  
% 3.64/1.58  Simplification rules
% 3.64/1.58  ----------------------
% 3.64/1.58  #Subsume      : 96
% 3.64/1.58  #Demod        : 199
% 3.64/1.58  #Tautology    : 124
% 3.64/1.58  #SimpNegUnit  : 17
% 3.64/1.58  #BackRed      : 6
% 3.64/1.58  
% 3.64/1.58  #Partial instantiations: 0
% 3.64/1.58  #Strategies tried      : 1
% 3.64/1.58  
% 3.64/1.58  Timing (in seconds)
% 3.64/1.58  ----------------------
% 3.64/1.58  Preprocessing        : 0.33
% 3.64/1.58  Parsing              : 0.17
% 3.64/1.58  CNF conversion       : 0.02
% 3.64/1.58  Main loop            : 0.50
% 3.64/1.58  Inferencing          : 0.19
% 3.64/1.58  Reduction            : 0.14
% 3.64/1.58  Demodulation         : 0.10
% 3.64/1.58  BG Simplification    : 0.03
% 3.64/1.58  Subsumption          : 0.10
% 3.64/1.58  Abstraction          : 0.03
% 3.64/1.58  MUC search           : 0.00
% 3.64/1.58  Cooper               : 0.00
% 3.64/1.58  Total                : 0.86
% 3.64/1.58  Index Insertion      : 0.00
% 3.64/1.58  Index Deletion       : 0.00
% 3.64/1.58  Index Matching       : 0.00
% 3.64/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
