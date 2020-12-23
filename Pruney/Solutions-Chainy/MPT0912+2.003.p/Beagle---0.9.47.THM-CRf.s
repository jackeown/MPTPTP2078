%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 136 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_20,plain,(
    r2_hidden('#skF_4',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( r2_hidden('#skF_3'(A_6,B_7,C_8,D_9),C_8)
      | ~ r2_hidden(D_9,A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8,D_9),B_7)
      | ~ r2_hidden(D_9,A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k4_tarski('#skF_2'(A_6,B_7,C_8,D_9),'#skF_3'(A_6,B_7,C_8,D_9)) = D_9
      | ~ r2_hidden(D_9,A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k4_tarski('#skF_2'(A_79,B_80,C_81,D_82),'#skF_3'(A_79,B_80,C_81,D_82)) = D_82
      | ~ r2_hidden(D_82,A_79)
      | ~ r1_tarski(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k4_tarski(k4_tarski(A_12,B_13),C_14) = k3_mcart_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [A_96,D_95,B_99,C_97,C_98] :
      ( k3_mcart_1('#skF_2'(A_96,B_99,C_97,D_95),'#skF_3'(A_96,B_99,C_97,D_95),C_98) = k4_tarski(D_95,C_98)
      | ~ r2_hidden(D_95,A_96)
      | ~ r1_tarski(A_96,k2_zfmisc_1(B_99,C_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_14])).

tff(c_18,plain,(
    ! [E_21,F_22,G_23] :
      ( k3_mcart_1(E_21,F_22,G_23) != '#skF_4'
      | ~ r2_hidden(G_23,'#skF_7')
      | ~ r2_hidden(F_22,'#skF_6')
      | ~ r2_hidden(E_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_195,plain,(
    ! [B_107,C_108,A_109,C_106,D_110] :
      ( k4_tarski(D_110,C_106) != '#skF_4'
      | ~ r2_hidden(C_106,'#skF_7')
      | ~ r2_hidden('#skF_3'(A_109,B_107,C_108,D_110),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_109,B_107,C_108,D_110),'#skF_5')
      | ~ r2_hidden(D_110,A_109)
      | ~ r1_tarski(A_109,k2_zfmisc_1(B_107,C_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_18])).

tff(c_323,plain,(
    ! [B_166,C_165,C_162,B_167,A_164,D_163,A_168] :
      ( D_163 != '#skF_4'
      | ~ r2_hidden('#skF_3'(A_168,B_167,C_165,D_163),'#skF_7')
      | ~ r2_hidden('#skF_3'(A_164,B_166,C_162,'#skF_2'(A_168,B_167,C_165,D_163)),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_164,B_166,C_162,'#skF_2'(A_168,B_167,C_165,D_163)),'#skF_5')
      | ~ r2_hidden('#skF_2'(A_168,B_167,C_165,D_163),A_164)
      | ~ r1_tarski(A_164,k2_zfmisc_1(B_166,C_162))
      | ~ r2_hidden(D_163,A_168)
      | ~ r1_tarski(A_168,k2_zfmisc_1(B_167,C_165)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_387,plain,(
    ! [A_191,A_190,C_188,D_187,B_186,C_189] :
      ( D_187 != '#skF_4'
      | ~ r2_hidden('#skF_3'(A_190,B_186,C_188,D_187),'#skF_7')
      | ~ r2_hidden('#skF_3'(A_191,'#skF_5',C_189,'#skF_2'(A_190,B_186,C_188,D_187)),'#skF_6')
      | ~ r2_hidden(D_187,A_190)
      | ~ r1_tarski(A_190,k2_zfmisc_1(B_186,C_188))
      | ~ r2_hidden('#skF_2'(A_190,B_186,C_188,D_187),A_191)
      | ~ r1_tarski(A_191,k2_zfmisc_1('#skF_5',C_189)) ) ),
    inference(resolution,[status(thm)],[c_12,c_323])).

tff(c_422,plain,(
    ! [C_204,D_201,A_203,A_205,B_202] :
      ( D_201 != '#skF_4'
      | ~ r2_hidden('#skF_3'(A_203,B_202,C_204,D_201),'#skF_7')
      | ~ r2_hidden(D_201,A_203)
      | ~ r1_tarski(A_203,k2_zfmisc_1(B_202,C_204))
      | ~ r2_hidden('#skF_2'(A_203,B_202,C_204,D_201),A_205)
      | ~ r1_tarski(A_205,k2_zfmisc_1('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_10,c_387])).

tff(c_432,plain,(
    ! [D_206,A_207,B_208,C_209] :
      ( D_206 != '#skF_4'
      | ~ r2_hidden('#skF_3'(A_207,B_208,C_209,D_206),'#skF_7')
      | ~ r1_tarski(B_208,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(D_206,A_207)
      | ~ r1_tarski(A_207,k2_zfmisc_1(B_208,C_209)) ) ),
    inference(resolution,[status(thm)],[c_12,c_422])).

tff(c_444,plain,(
    ! [D_210,B_211,A_212] :
      ( D_210 != '#skF_4'
      | ~ r1_tarski(B_211,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(D_210,A_212)
      | ~ r1_tarski(A_212,k2_zfmisc_1(B_211,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_10,c_432])).

tff(c_447,plain,(
    ! [D_210,A_212] :
      ( D_210 != '#skF_4'
      | ~ r2_hidden(D_210,A_212)
      | ~ r1_tarski(A_212,k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_27,c_444])).

tff(c_451,plain,(
    ! [D_213,A_214] :
      ( D_213 != '#skF_4'
      | ~ r2_hidden(D_213,A_214)
      | ~ r1_tarski(A_214,k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_447])).

tff(c_465,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_5','#skF_6','#skF_7'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_20,c_451])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  %$ r2_hidden > r1_tarski > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.45  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.45  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.45  
% 2.81/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.46  tff(f_63, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 2.81/1.46  tff(f_49, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.81/1.46  tff(f_45, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.81/1.46  tff(f_47, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.81/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.46  tff(c_22, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.46  tff(c_27, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_22])).
% 2.81/1.46  tff(c_20, plain, (r2_hidden('#skF_4', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.46  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.81/1.46  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (r2_hidden('#skF_3'(A_6, B_7, C_8, D_9), C_8) | ~r2_hidden(D_9, A_6) | ~r1_tarski(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.46  tff(c_12, plain, (![A_6, B_7, C_8, D_9]: (r2_hidden('#skF_2'(A_6, B_7, C_8, D_9), B_7) | ~r2_hidden(D_9, A_6) | ~r1_tarski(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.46  tff(c_8, plain, (![A_6, B_7, C_8, D_9]: (k4_tarski('#skF_2'(A_6, B_7, C_8, D_9), '#skF_3'(A_6, B_7, C_8, D_9))=D_9 | ~r2_hidden(D_9, A_6) | ~r1_tarski(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.46  tff(c_137, plain, (![A_79, B_80, C_81, D_82]: (k4_tarski('#skF_2'(A_79, B_80, C_81, D_82), '#skF_3'(A_79, B_80, C_81, D_82))=D_82 | ~r2_hidden(D_82, A_79) | ~r1_tarski(A_79, k2_zfmisc_1(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.46  tff(c_14, plain, (![A_12, B_13, C_14]: (k4_tarski(k4_tarski(A_12, B_13), C_14)=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.46  tff(c_160, plain, (![A_96, D_95, B_99, C_97, C_98]: (k3_mcart_1('#skF_2'(A_96, B_99, C_97, D_95), '#skF_3'(A_96, B_99, C_97, D_95), C_98)=k4_tarski(D_95, C_98) | ~r2_hidden(D_95, A_96) | ~r1_tarski(A_96, k2_zfmisc_1(B_99, C_97)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_14])).
% 2.81/1.46  tff(c_18, plain, (![E_21, F_22, G_23]: (k3_mcart_1(E_21, F_22, G_23)!='#skF_4' | ~r2_hidden(G_23, '#skF_7') | ~r2_hidden(F_22, '#skF_6') | ~r2_hidden(E_21, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.46  tff(c_195, plain, (![B_107, C_108, A_109, C_106, D_110]: (k4_tarski(D_110, C_106)!='#skF_4' | ~r2_hidden(C_106, '#skF_7') | ~r2_hidden('#skF_3'(A_109, B_107, C_108, D_110), '#skF_6') | ~r2_hidden('#skF_2'(A_109, B_107, C_108, D_110), '#skF_5') | ~r2_hidden(D_110, A_109) | ~r1_tarski(A_109, k2_zfmisc_1(B_107, C_108)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_18])).
% 2.81/1.46  tff(c_323, plain, (![B_166, C_165, C_162, B_167, A_164, D_163, A_168]: (D_163!='#skF_4' | ~r2_hidden('#skF_3'(A_168, B_167, C_165, D_163), '#skF_7') | ~r2_hidden('#skF_3'(A_164, B_166, C_162, '#skF_2'(A_168, B_167, C_165, D_163)), '#skF_6') | ~r2_hidden('#skF_2'(A_164, B_166, C_162, '#skF_2'(A_168, B_167, C_165, D_163)), '#skF_5') | ~r2_hidden('#skF_2'(A_168, B_167, C_165, D_163), A_164) | ~r1_tarski(A_164, k2_zfmisc_1(B_166, C_162)) | ~r2_hidden(D_163, A_168) | ~r1_tarski(A_168, k2_zfmisc_1(B_167, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_195])).
% 2.81/1.46  tff(c_387, plain, (![A_191, A_190, C_188, D_187, B_186, C_189]: (D_187!='#skF_4' | ~r2_hidden('#skF_3'(A_190, B_186, C_188, D_187), '#skF_7') | ~r2_hidden('#skF_3'(A_191, '#skF_5', C_189, '#skF_2'(A_190, B_186, C_188, D_187)), '#skF_6') | ~r2_hidden(D_187, A_190) | ~r1_tarski(A_190, k2_zfmisc_1(B_186, C_188)) | ~r2_hidden('#skF_2'(A_190, B_186, C_188, D_187), A_191) | ~r1_tarski(A_191, k2_zfmisc_1('#skF_5', C_189)))), inference(resolution, [status(thm)], [c_12, c_323])).
% 2.81/1.46  tff(c_422, plain, (![C_204, D_201, A_203, A_205, B_202]: (D_201!='#skF_4' | ~r2_hidden('#skF_3'(A_203, B_202, C_204, D_201), '#skF_7') | ~r2_hidden(D_201, A_203) | ~r1_tarski(A_203, k2_zfmisc_1(B_202, C_204)) | ~r2_hidden('#skF_2'(A_203, B_202, C_204, D_201), A_205) | ~r1_tarski(A_205, k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_10, c_387])).
% 2.81/1.46  tff(c_432, plain, (![D_206, A_207, B_208, C_209]: (D_206!='#skF_4' | ~r2_hidden('#skF_3'(A_207, B_208, C_209, D_206), '#skF_7') | ~r1_tarski(B_208, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(D_206, A_207) | ~r1_tarski(A_207, k2_zfmisc_1(B_208, C_209)))), inference(resolution, [status(thm)], [c_12, c_422])).
% 2.81/1.46  tff(c_444, plain, (![D_210, B_211, A_212]: (D_210!='#skF_4' | ~r1_tarski(B_211, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(D_210, A_212) | ~r1_tarski(A_212, k2_zfmisc_1(B_211, '#skF_7')))), inference(resolution, [status(thm)], [c_10, c_432])).
% 2.81/1.46  tff(c_447, plain, (![D_210, A_212]: (D_210!='#skF_4' | ~r2_hidden(D_210, A_212) | ~r1_tarski(A_212, k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')))), inference(resolution, [status(thm)], [c_27, c_444])).
% 2.81/1.46  tff(c_451, plain, (![D_213, A_214]: (D_213!='#skF_4' | ~r2_hidden(D_213, A_214) | ~r1_tarski(A_214, k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_447])).
% 2.81/1.46  tff(c_465, plain, (~r1_tarski(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_20, c_451])).
% 2.81/1.46  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_465])).
% 2.81/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  Inference rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Ref     : 0
% 2.81/1.46  #Sup     : 126
% 2.81/1.46  #Fact    : 0
% 2.81/1.46  #Define  : 0
% 2.81/1.46  #Split   : 0
% 2.81/1.46  #Chain   : 0
% 2.81/1.46  #Close   : 0
% 2.81/1.46  
% 2.81/1.46  Ordering : KBO
% 2.81/1.46  
% 2.81/1.46  Simplification rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Subsume      : 8
% 2.81/1.46  #Demod        : 56
% 2.81/1.46  #Tautology    : 37
% 2.81/1.46  #SimpNegUnit  : 0
% 2.81/1.46  #BackRed      : 0
% 2.81/1.46  
% 2.81/1.46  #Partial instantiations: 0
% 2.81/1.46  #Strategies tried      : 1
% 2.81/1.46  
% 2.81/1.46  Timing (in seconds)
% 2.81/1.46  ----------------------
% 3.14/1.47  Preprocessing        : 0.27
% 3.14/1.47  Parsing              : 0.15
% 3.14/1.47  CNF conversion       : 0.02
% 3.14/1.47  Main loop            : 0.43
% 3.14/1.47  Inferencing          : 0.19
% 3.14/1.47  Reduction            : 0.11
% 3.14/1.47  Demodulation         : 0.09
% 3.14/1.47  BG Simplification    : 0.02
% 3.14/1.47  Subsumption          : 0.09
% 3.14/1.47  Abstraction          : 0.02
% 3.14/1.47  MUC search           : 0.00
% 3.14/1.47  Cooper               : 0.00
% 3.14/1.47  Total                : 0.74
% 3.14/1.47  Index Insertion      : 0.00
% 3.14/1.47  Index Deletion       : 0.00
% 3.14/1.47  Index Matching       : 0.00
% 3.14/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
