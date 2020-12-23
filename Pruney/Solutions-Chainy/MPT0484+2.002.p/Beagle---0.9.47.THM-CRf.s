%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:32 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 181 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k2_relat_1(B),A)
         => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(c_34,plain,(
    k5_relat_1('#skF_5',k6_relat_1('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(k4_tarski('#skF_2'(A_65,B_66),'#skF_3'(A_65,B_66)),A_65)
      | r1_tarski(A_65,B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [B_26,C_27,A_25] :
      ( r2_hidden(B_26,k2_relat_1(C_27))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_3'(A_71,B_72),k2_relat_1(A_71))
      | r1_tarski(A_71,B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_86,c_20])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_3'(A_76,B_77),B_78)
      | ~ r1_tarski(k2_relat_1(A_76),B_78)
      | r1_tarski(A_76,B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_317,plain,(
    ! [A_132,B_133,B_134,B_135] :
      ( r2_hidden('#skF_3'(A_132,B_133),B_134)
      | ~ r1_tarski(B_135,B_134)
      | ~ r1_tarski(k2_relat_1(A_132),B_135)
      | r1_tarski(A_132,B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_342,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_3'(A_141,B_142),'#skF_4')
      | ~ r1_tarski(k2_relat_1(A_141),k2_relat_1('#skF_5'))
      | r1_tarski(A_141,B_142)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_36,c_317])).

tff(c_345,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_3'('#skF_5',B_142),'#skF_4')
      | r1_tarski('#skF_5',B_142)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_342])).

tff(c_348,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_3'('#skF_5',B_142),'#skF_4')
      | r1_tarski('#skF_5',B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_345])).

tff(c_18,plain,(
    ! [A_8,B_18] :
      ( r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),A_8)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    ! [A_103,B_104,D_105,C_106] :
      ( r2_hidden(k4_tarski(A_103,B_104),k5_relat_1(D_105,k6_relat_1(C_106)))
      | ~ r2_hidden(k4_tarski(A_103,B_104),D_105)
      | ~ r2_hidden(B_104,C_106)
      | ~ v1_relat_1(D_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_8,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),B_18)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_927,plain,(
    ! [A_293,D_294,C_295] :
      ( r1_tarski(A_293,k5_relat_1(D_294,k6_relat_1(C_295)))
      | ~ v1_relat_1(A_293)
      | ~ r2_hidden(k4_tarski('#skF_2'(A_293,k5_relat_1(D_294,k6_relat_1(C_295))),'#skF_3'(A_293,k5_relat_1(D_294,k6_relat_1(C_295)))),D_294)
      | ~ r2_hidden('#skF_3'(A_293,k5_relat_1(D_294,k6_relat_1(C_295))),C_295)
      | ~ v1_relat_1(D_294) ) ),
    inference(resolution,[status(thm)],[c_212,c_16])).

tff(c_958,plain,(
    ! [A_296,C_297] :
      ( ~ r2_hidden('#skF_3'(A_296,k5_relat_1(A_296,k6_relat_1(C_297))),C_297)
      | r1_tarski(A_296,k5_relat_1(A_296,k6_relat_1(C_297)))
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_18,c_927])).

tff(c_982,plain,
    ( ~ v1_relat_1('#skF_5')
    | r1_tarski('#skF_5',k5_relat_1('#skF_5',k6_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_348,c_958])).

tff(c_1004,plain,(
    r1_tarski('#skF_5',k5_relat_1('#skF_5',k6_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_982])).

tff(c_32,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k5_relat_1(B_33,k6_relat_1(A_32)),B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_56)
      | ~ r1_tarski(A_54,B_56)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_126,plain,(
    ! [A_79,B_80,B_81,B_82] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(B_82,B_81)
      | ~ r1_tarski(A_79,B_82)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_199,plain,(
    ! [A_99,B_100,B_101,A_102] :
      ( r2_hidden('#skF_1'(A_99,B_100),B_101)
      | ~ r1_tarski(A_99,k5_relat_1(B_101,k6_relat_1(A_102)))
      | r1_tarski(A_99,B_100)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_32,c_126])).

tff(c_246,plain,(
    ! [B_110,A_111,B_112] :
      ( r2_hidden('#skF_1'(k5_relat_1(B_110,k6_relat_1(A_111)),B_112),B_110)
      | r1_tarski(k5_relat_1(B_110,k6_relat_1(A_111)),B_112)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_199])).

tff(c_551,plain,(
    ! [B_217,A_218,B_219,B_220] :
      ( r2_hidden('#skF_1'(k5_relat_1(B_217,k6_relat_1(A_218)),B_219),B_220)
      | ~ r1_tarski(B_217,B_220)
      | r1_tarski(k5_relat_1(B_217,k6_relat_1(A_218)),B_219)
      | ~ v1_relat_1(B_217) ) ),
    inference(resolution,[status(thm)],[c_246,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_560,plain,(
    ! [B_221,B_222,A_223] :
      ( ~ r1_tarski(B_221,B_222)
      | r1_tarski(k5_relat_1(B_221,k6_relat_1(A_223)),B_222)
      | ~ v1_relat_1(B_221) ) ),
    inference(resolution,[status(thm)],[c_551,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_616,plain,(
    ! [B_221,A_223,B_222] :
      ( k5_relat_1(B_221,k6_relat_1(A_223)) = B_222
      | ~ r1_tarski(B_222,k5_relat_1(B_221,k6_relat_1(A_223)))
      | ~ r1_tarski(B_221,B_222)
      | ~ v1_relat_1(B_221) ) ),
    inference(resolution,[status(thm)],[c_560,c_8])).

tff(c_1016,plain,
    ( k5_relat_1('#skF_5',k6_relat_1('#skF_4')) = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1004,c_616])).

tff(c_1047,plain,(
    k5_relat_1('#skF_5',k6_relat_1('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12,c_1016])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.64  
% 4.15/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.64  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.15/1.64  
% 4.15/1.64  %Foreground sorts:
% 4.15/1.64  
% 4.15/1.64  
% 4.15/1.64  %Background operators:
% 4.15/1.64  
% 4.15/1.64  
% 4.15/1.64  %Foreground operators:
% 4.15/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.15/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.15/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.15/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.15/1.64  tff('#skF_5', type, '#skF_5': $i).
% 4.15/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.15/1.64  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.15/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.15/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.15/1.64  
% 4.15/1.66  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.15/1.66  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.15/1.66  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 4.15/1.66  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 4.15/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.15/1.66  tff(f_64, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_relat_1)).
% 4.15/1.66  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 4.15/1.66  tff(c_34, plain, (k5_relat_1('#skF_5', k6_relat_1('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.66  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.66  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.66  tff(c_36, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.66  tff(c_86, plain, (![A_65, B_66]: (r2_hidden(k4_tarski('#skF_2'(A_65, B_66), '#skF_3'(A_65, B_66)), A_65) | r1_tarski(A_65, B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.66  tff(c_20, plain, (![B_26, C_27, A_25]: (r2_hidden(B_26, k2_relat_1(C_27)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.15/1.66  tff(c_114, plain, (![A_71, B_72]: (r2_hidden('#skF_3'(A_71, B_72), k2_relat_1(A_71)) | r1_tarski(A_71, B_72) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_86, c_20])).
% 4.15/1.66  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.66  tff(c_122, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_3'(A_76, B_77), B_78) | ~r1_tarski(k2_relat_1(A_76), B_78) | r1_tarski(A_76, B_77) | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_114, c_2])).
% 4.15/1.66  tff(c_317, plain, (![A_132, B_133, B_134, B_135]: (r2_hidden('#skF_3'(A_132, B_133), B_134) | ~r1_tarski(B_135, B_134) | ~r1_tarski(k2_relat_1(A_132), B_135) | r1_tarski(A_132, B_133) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_122, c_2])).
% 4.15/1.66  tff(c_342, plain, (![A_141, B_142]: (r2_hidden('#skF_3'(A_141, B_142), '#skF_4') | ~r1_tarski(k2_relat_1(A_141), k2_relat_1('#skF_5')) | r1_tarski(A_141, B_142) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_36, c_317])).
% 4.15/1.66  tff(c_345, plain, (![B_142]: (r2_hidden('#skF_3'('#skF_5', B_142), '#skF_4') | r1_tarski('#skF_5', B_142) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_342])).
% 4.15/1.66  tff(c_348, plain, (![B_142]: (r2_hidden('#skF_3'('#skF_5', B_142), '#skF_4') | r1_tarski('#skF_5', B_142))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_345])).
% 4.15/1.66  tff(c_18, plain, (![A_8, B_18]: (r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), A_8) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.66  tff(c_212, plain, (![A_103, B_104, D_105, C_106]: (r2_hidden(k4_tarski(A_103, B_104), k5_relat_1(D_105, k6_relat_1(C_106))) | ~r2_hidden(k4_tarski(A_103, B_104), D_105) | ~r2_hidden(B_104, C_106) | ~v1_relat_1(D_105))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.15/1.66  tff(c_16, plain, (![A_8, B_18]: (~r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), B_18) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.66  tff(c_927, plain, (![A_293, D_294, C_295]: (r1_tarski(A_293, k5_relat_1(D_294, k6_relat_1(C_295))) | ~v1_relat_1(A_293) | ~r2_hidden(k4_tarski('#skF_2'(A_293, k5_relat_1(D_294, k6_relat_1(C_295))), '#skF_3'(A_293, k5_relat_1(D_294, k6_relat_1(C_295)))), D_294) | ~r2_hidden('#skF_3'(A_293, k5_relat_1(D_294, k6_relat_1(C_295))), C_295) | ~v1_relat_1(D_294))), inference(resolution, [status(thm)], [c_212, c_16])).
% 4.15/1.66  tff(c_958, plain, (![A_296, C_297]: (~r2_hidden('#skF_3'(A_296, k5_relat_1(A_296, k6_relat_1(C_297))), C_297) | r1_tarski(A_296, k5_relat_1(A_296, k6_relat_1(C_297))) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_18, c_927])).
% 4.15/1.66  tff(c_982, plain, (~v1_relat_1('#skF_5') | r1_tarski('#skF_5', k5_relat_1('#skF_5', k6_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_348, c_958])).
% 4.15/1.66  tff(c_1004, plain, (r1_tarski('#skF_5', k5_relat_1('#skF_5', k6_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_982])).
% 4.15/1.66  tff(c_32, plain, (![B_33, A_32]: (r1_tarski(k5_relat_1(B_33, k6_relat_1(A_32)), B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.15/1.66  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.66  tff(c_68, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.66  tff(c_74, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_1'(A_54, B_55), B_56) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_6, c_68])).
% 4.15/1.66  tff(c_126, plain, (![A_79, B_80, B_81, B_82]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(B_82, B_81) | ~r1_tarski(A_79, B_82) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_74, c_2])).
% 4.15/1.66  tff(c_199, plain, (![A_99, B_100, B_101, A_102]: (r2_hidden('#skF_1'(A_99, B_100), B_101) | ~r1_tarski(A_99, k5_relat_1(B_101, k6_relat_1(A_102))) | r1_tarski(A_99, B_100) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_32, c_126])).
% 4.15/1.66  tff(c_246, plain, (![B_110, A_111, B_112]: (r2_hidden('#skF_1'(k5_relat_1(B_110, k6_relat_1(A_111)), B_112), B_110) | r1_tarski(k5_relat_1(B_110, k6_relat_1(A_111)), B_112) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_12, c_199])).
% 4.15/1.66  tff(c_551, plain, (![B_217, A_218, B_219, B_220]: (r2_hidden('#skF_1'(k5_relat_1(B_217, k6_relat_1(A_218)), B_219), B_220) | ~r1_tarski(B_217, B_220) | r1_tarski(k5_relat_1(B_217, k6_relat_1(A_218)), B_219) | ~v1_relat_1(B_217))), inference(resolution, [status(thm)], [c_246, c_2])).
% 4.15/1.66  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.66  tff(c_560, plain, (![B_221, B_222, A_223]: (~r1_tarski(B_221, B_222) | r1_tarski(k5_relat_1(B_221, k6_relat_1(A_223)), B_222) | ~v1_relat_1(B_221))), inference(resolution, [status(thm)], [c_551, c_4])).
% 4.15/1.66  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.66  tff(c_616, plain, (![B_221, A_223, B_222]: (k5_relat_1(B_221, k6_relat_1(A_223))=B_222 | ~r1_tarski(B_222, k5_relat_1(B_221, k6_relat_1(A_223))) | ~r1_tarski(B_221, B_222) | ~v1_relat_1(B_221))), inference(resolution, [status(thm)], [c_560, c_8])).
% 4.15/1.66  tff(c_1016, plain, (k5_relat_1('#skF_5', k6_relat_1('#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', '#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1004, c_616])).
% 4.15/1.66  tff(c_1047, plain, (k5_relat_1('#skF_5', k6_relat_1('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12, c_1016])).
% 4.15/1.66  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1047])).
% 4.15/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.66  
% 4.15/1.66  Inference rules
% 4.15/1.66  ----------------------
% 4.15/1.66  #Ref     : 0
% 4.15/1.66  #Sup     : 244
% 4.15/1.66  #Fact    : 0
% 4.15/1.66  #Define  : 0
% 4.15/1.66  #Split   : 3
% 4.15/1.66  #Chain   : 0
% 4.15/1.66  #Close   : 0
% 4.15/1.66  
% 4.15/1.66  Ordering : KBO
% 4.15/1.66  
% 4.15/1.66  Simplification rules
% 4.15/1.66  ----------------------
% 4.15/1.66  #Subsume      : 38
% 4.15/1.66  #Demod        : 13
% 4.15/1.66  #Tautology    : 12
% 4.15/1.66  #SimpNegUnit  : 1
% 4.15/1.66  #BackRed      : 0
% 4.15/1.66  
% 4.15/1.66  #Partial instantiations: 0
% 4.15/1.66  #Strategies tried      : 1
% 4.15/1.66  
% 4.15/1.66  Timing (in seconds)
% 4.15/1.66  ----------------------
% 4.15/1.66  Preprocessing        : 0.28
% 4.15/1.66  Parsing              : 0.15
% 4.15/1.66  CNF conversion       : 0.02
% 4.15/1.66  Main loop            : 0.61
% 4.15/1.66  Inferencing          : 0.21
% 4.15/1.66  Reduction            : 0.13
% 4.15/1.66  Demodulation         : 0.08
% 4.15/1.66  BG Simplification    : 0.02
% 4.15/1.66  Subsumption          : 0.22
% 4.15/1.66  Abstraction          : 0.02
% 4.15/1.66  MUC search           : 0.00
% 4.15/1.66  Cooper               : 0.00
% 4.15/1.66  Total                : 0.93
% 4.15/1.66  Index Insertion      : 0.00
% 4.15/1.66  Index Deletion       : 0.00
% 4.15/1.66  Index Matching       : 0.00
% 4.15/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
