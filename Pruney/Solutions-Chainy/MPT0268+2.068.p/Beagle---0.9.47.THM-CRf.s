%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 7.17s
% Output     : CNFRefutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 204 expanded)
%              Number of equality atoms :   33 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_30,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_39,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_361,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63,C_64),C_64)
      | r2_hidden('#skF_2'(A_62,B_63,C_64),C_64)
      | k4_xboole_0(A_62,B_63) = C_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_374,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_361])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_789,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r2_hidden('#skF_1'(A_76,B_77,C_78),C_78)
      | r2_hidden('#skF_2'(A_76,B_77,C_78),B_77)
      | ~ r2_hidden('#skF_2'(A_76,B_77,C_78),A_76)
      | k4_xboole_0(A_76,B_77) = C_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5257,plain,(
    ! [A_175,B_176] :
      ( r2_hidden('#skF_2'(A_175,B_176,A_175),B_176)
      | ~ r2_hidden('#skF_2'(A_175,B_176,A_175),A_175)
      | k4_xboole_0(A_175,B_176) = A_175 ) ),
    inference(resolution,[status(thm)],[c_12,c_789])).

tff(c_5275,plain,(
    ! [A_177,B_178] :
      ( r2_hidden('#skF_2'(A_177,B_178,A_177),B_178)
      | k4_xboole_0(A_177,B_178) = A_177 ) ),
    inference(resolution,[status(thm)],[c_374,c_5257])).

tff(c_43,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(k1_tarski(A_22),B_23) = k1_tarski(A_22)
      | r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [C_11,B_10] : ~ r2_hidden(C_11,k4_xboole_0(B_10,k1_tarski(C_11))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [C_11,A_22] :
      ( ~ r2_hidden(C_11,k1_tarski(A_22))
      | r2_hidden(A_22,k1_tarski(C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_26])).

tff(c_5302,plain,(
    ! [A_22,A_177] :
      ( r2_hidden(A_22,k1_tarski('#skF_2'(A_177,k1_tarski(A_22),A_177)))
      | k4_xboole_0(A_177,k1_tarski(A_22)) = A_177 ) ),
    inference(resolution,[status(thm)],[c_5275,c_59])).

tff(c_24,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(A_9,k4_xboole_0(B_10,k1_tarski(C_11)))
      | C_11 = A_9
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_185,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r2_hidden('#skF_1'(A_51,B_52,C_53),B_52)
      | r2_hidden('#skF_2'(A_51,B_52,C_53),C_53)
      | k4_xboole_0(A_51,B_52) = C_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_198,plain,(
    ! [A_54,C_55] :
      ( r2_hidden('#skF_2'(A_54,A_54,C_55),C_55)
      | k4_xboole_0(A_54,A_54) = C_55 ) ),
    inference(resolution,[status(thm)],[c_18,c_185])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5363,plain,(
    ! [A_184,A_185,B_186] :
      ( r2_hidden('#skF_2'(A_184,A_184,k4_xboole_0(A_185,B_186)),A_185)
      | k4_xboole_0(A_185,B_186) = k4_xboole_0(A_184,A_184) ) ),
    inference(resolution,[status(thm)],[c_198,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [D_6,B_23,A_22] :
      ( ~ r2_hidden(D_6,B_23)
      | ~ r2_hidden(D_6,k1_tarski(A_22))
      | r2_hidden(A_22,B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_4])).

tff(c_227,plain,(
    ! [A_54,C_55,A_22] :
      ( ~ r2_hidden('#skF_2'(A_54,A_54,C_55),k1_tarski(A_22))
      | r2_hidden(A_22,C_55)
      | k4_xboole_0(A_54,A_54) = C_55 ) ),
    inference(resolution,[status(thm)],[c_198,c_52])).

tff(c_5401,plain,(
    ! [A_187,B_188,A_189] :
      ( r2_hidden(A_187,k4_xboole_0(k1_tarski(A_187),B_188))
      | k4_xboole_0(k1_tarski(A_187),B_188) = k4_xboole_0(A_189,A_189) ) ),
    inference(resolution,[status(thm)],[c_5363,c_227])).

tff(c_5531,plain,(
    ! [A_190,A_191] : k4_xboole_0(k1_tarski(A_190),k1_tarski(A_190)) = k4_xboole_0(A_191,A_191) ),
    inference(resolution,[status(thm)],[c_5401,c_26])).

tff(c_5649,plain,(
    ! [A_192,A_193] : ~ r2_hidden(A_192,k4_xboole_0(A_193,A_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5531,c_26])).

tff(c_6001,plain,(
    ! [C_202,A_203] :
      ( C_202 = A_203
      | ~ r2_hidden(A_203,k1_tarski(C_202)) ) ),
    inference(resolution,[status(thm)],[c_24,c_5649])).

tff(c_10360,plain,(
    ! [A_291,A_292] :
      ( '#skF_2'(A_291,k1_tarski(A_292),A_291) = A_292
      | k4_xboole_0(A_291,k1_tarski(A_292)) = A_291 ) ),
    inference(resolution,[status(thm)],[c_5302,c_6001])).

tff(c_10568,plain,(
    '#skF_2'('#skF_3',k1_tarski('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10360,c_39])).

tff(c_10586,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10568,c_374])).

tff(c_10598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_37,c_10586])).

tff(c_10599,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_10600,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10613,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10600,c_34])).

tff(c_10620,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10613,c_26])).

tff(c_10625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10599,c_10620])).

tff(c_10626,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_10627,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10632,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10627,c_36])).

tff(c_10639,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10632,c_26])).

tff(c_10644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10626,c_10639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:46:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.17/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.17/2.56  
% 7.17/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.17/2.56  %$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 7.17/2.56  
% 7.17/2.56  %Foreground sorts:
% 7.17/2.56  
% 7.17/2.56  
% 7.17/2.56  %Background operators:
% 7.17/2.56  
% 7.17/2.56  
% 7.17/2.56  %Foreground operators:
% 7.17/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.17/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.17/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.17/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.17/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.17/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.17/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.17/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.17/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.17/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.17/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.17/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.17/2.56  
% 7.17/2.57  tff(f_53, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.17/2.57  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.17/2.57  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 7.17/2.57  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.17/2.57  tff(c_30, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.17/2.57  tff(c_39, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 7.17/2.57  tff(c_32, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.17/2.57  tff(c_37, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 7.17/2.57  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_361, plain, (![A_62, B_63, C_64]: (~r2_hidden('#skF_1'(A_62, B_63, C_64), C_64) | r2_hidden('#skF_2'(A_62, B_63, C_64), C_64) | k4_xboole_0(A_62, B_63)=C_64)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_374, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_361])).
% 7.17/2.57  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_789, plain, (![A_76, B_77, C_78]: (~r2_hidden('#skF_1'(A_76, B_77, C_78), C_78) | r2_hidden('#skF_2'(A_76, B_77, C_78), B_77) | ~r2_hidden('#skF_2'(A_76, B_77, C_78), A_76) | k4_xboole_0(A_76, B_77)=C_78)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_5257, plain, (![A_175, B_176]: (r2_hidden('#skF_2'(A_175, B_176, A_175), B_176) | ~r2_hidden('#skF_2'(A_175, B_176, A_175), A_175) | k4_xboole_0(A_175, B_176)=A_175)), inference(resolution, [status(thm)], [c_12, c_789])).
% 7.17/2.57  tff(c_5275, plain, (![A_177, B_178]: (r2_hidden('#skF_2'(A_177, B_178, A_177), B_178) | k4_xboole_0(A_177, B_178)=A_177)), inference(resolution, [status(thm)], [c_374, c_5257])).
% 7.17/2.57  tff(c_43, plain, (![A_22, B_23]: (k4_xboole_0(k1_tarski(A_22), B_23)=k1_tarski(A_22) | r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.17/2.57  tff(c_26, plain, (![C_11, B_10]: (~r2_hidden(C_11, k4_xboole_0(B_10, k1_tarski(C_11))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.17/2.57  tff(c_59, plain, (![C_11, A_22]: (~r2_hidden(C_11, k1_tarski(A_22)) | r2_hidden(A_22, k1_tarski(C_11)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_26])).
% 7.17/2.57  tff(c_5302, plain, (![A_22, A_177]: (r2_hidden(A_22, k1_tarski('#skF_2'(A_177, k1_tarski(A_22), A_177))) | k4_xboole_0(A_177, k1_tarski(A_22))=A_177)), inference(resolution, [status(thm)], [c_5275, c_59])).
% 7.17/2.57  tff(c_24, plain, (![A_9, B_10, C_11]: (r2_hidden(A_9, k4_xboole_0(B_10, k1_tarski(C_11))) | C_11=A_9 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.17/2.57  tff(c_185, plain, (![A_51, B_52, C_53]: (~r2_hidden('#skF_1'(A_51, B_52, C_53), B_52) | r2_hidden('#skF_2'(A_51, B_52, C_53), C_53) | k4_xboole_0(A_51, B_52)=C_53)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_198, plain, (![A_54, C_55]: (r2_hidden('#skF_2'(A_54, A_54, C_55), C_55) | k4_xboole_0(A_54, A_54)=C_55)), inference(resolution, [status(thm)], [c_18, c_185])).
% 7.17/2.57  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_5363, plain, (![A_184, A_185, B_186]: (r2_hidden('#skF_2'(A_184, A_184, k4_xboole_0(A_185, B_186)), A_185) | k4_xboole_0(A_185, B_186)=k4_xboole_0(A_184, A_184))), inference(resolution, [status(thm)], [c_198, c_6])).
% 7.17/2.57  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.17/2.57  tff(c_52, plain, (![D_6, B_23, A_22]: (~r2_hidden(D_6, B_23) | ~r2_hidden(D_6, k1_tarski(A_22)) | r2_hidden(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_43, c_4])).
% 7.17/2.57  tff(c_227, plain, (![A_54, C_55, A_22]: (~r2_hidden('#skF_2'(A_54, A_54, C_55), k1_tarski(A_22)) | r2_hidden(A_22, C_55) | k4_xboole_0(A_54, A_54)=C_55)), inference(resolution, [status(thm)], [c_198, c_52])).
% 7.17/2.57  tff(c_5401, plain, (![A_187, B_188, A_189]: (r2_hidden(A_187, k4_xboole_0(k1_tarski(A_187), B_188)) | k4_xboole_0(k1_tarski(A_187), B_188)=k4_xboole_0(A_189, A_189))), inference(resolution, [status(thm)], [c_5363, c_227])).
% 7.17/2.57  tff(c_5531, plain, (![A_190, A_191]: (k4_xboole_0(k1_tarski(A_190), k1_tarski(A_190))=k4_xboole_0(A_191, A_191))), inference(resolution, [status(thm)], [c_5401, c_26])).
% 7.17/2.57  tff(c_5649, plain, (![A_192, A_193]: (~r2_hidden(A_192, k4_xboole_0(A_193, A_193)))), inference(superposition, [status(thm), theory('equality')], [c_5531, c_26])).
% 7.17/2.57  tff(c_6001, plain, (![C_202, A_203]: (C_202=A_203 | ~r2_hidden(A_203, k1_tarski(C_202)))), inference(resolution, [status(thm)], [c_24, c_5649])).
% 7.17/2.57  tff(c_10360, plain, (![A_291, A_292]: ('#skF_2'(A_291, k1_tarski(A_292), A_291)=A_292 | k4_xboole_0(A_291, k1_tarski(A_292))=A_291)), inference(resolution, [status(thm)], [c_5302, c_6001])).
% 7.17/2.57  tff(c_10568, plain, ('#skF_2'('#skF_3', k1_tarski('#skF_4'), '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10360, c_39])).
% 7.17/2.57  tff(c_10586, plain, (r2_hidden('#skF_4', '#skF_3') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10568, c_374])).
% 7.17/2.57  tff(c_10598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_37, c_10586])).
% 7.17/2.57  tff(c_10599, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 7.17/2.57  tff(c_10600, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 7.17/2.57  tff(c_34, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.17/2.57  tff(c_10613, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10600, c_34])).
% 7.17/2.57  tff(c_10620, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10613, c_26])).
% 7.17/2.57  tff(c_10625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10599, c_10620])).
% 7.17/2.57  tff(c_10626, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 7.17/2.57  tff(c_10627, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 7.17/2.57  tff(c_36, plain, (~r2_hidden('#skF_4', '#skF_3') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.17/2.57  tff(c_10632, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10627, c_36])).
% 7.17/2.57  tff(c_10639, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10632, c_26])).
% 7.17/2.57  tff(c_10644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10626, c_10639])).
% 7.17/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.17/2.57  
% 7.17/2.57  Inference rules
% 7.17/2.57  ----------------------
% 7.17/2.57  #Ref     : 1
% 7.17/2.57  #Sup     : 2904
% 7.17/2.57  #Fact    : 4
% 7.17/2.57  #Define  : 0
% 7.17/2.57  #Split   : 3
% 7.17/2.57  #Chain   : 0
% 7.17/2.57  #Close   : 0
% 7.17/2.57  
% 7.17/2.57  Ordering : KBO
% 7.17/2.57  
% 7.17/2.57  Simplification rules
% 7.17/2.57  ----------------------
% 7.17/2.58  #Subsume      : 1386
% 7.17/2.58  #Demod        : 594
% 7.17/2.58  #Tautology    : 391
% 7.17/2.58  #SimpNegUnit  : 244
% 7.17/2.58  #BackRed      : 1
% 7.17/2.58  
% 7.17/2.58  #Partial instantiations: 0
% 7.17/2.58  #Strategies tried      : 1
% 7.17/2.58  
% 7.17/2.58  Timing (in seconds)
% 7.17/2.58  ----------------------
% 7.17/2.58  Preprocessing        : 0.27
% 7.17/2.58  Parsing              : 0.14
% 7.17/2.58  CNF conversion       : 0.02
% 7.17/2.58  Main loop            : 1.45
% 7.17/2.58  Inferencing          : 0.50
% 7.17/2.58  Reduction            : 0.44
% 7.17/2.58  Demodulation         : 0.27
% 7.17/2.58  BG Simplification    : 0.06
% 7.17/2.58  Subsumption          : 0.36
% 7.17/2.58  Abstraction          : 0.10
% 7.17/2.58  MUC search           : 0.00
% 7.17/2.58  Cooper               : 0.00
% 7.17/2.58  Total                : 1.75
% 7.17/2.58  Index Insertion      : 0.00
% 7.17/2.58  Index Deletion       : 0.00
% 7.17/2.58  Index Matching       : 0.00
% 7.17/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
