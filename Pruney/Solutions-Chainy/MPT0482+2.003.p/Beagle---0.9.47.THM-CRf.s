%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:31 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.04s
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
       => ( r1_tarski(k1_relat_1(B),A)
         => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(k4_tarski('#skF_2'(A_65,B_66),'#skF_3'(A_65,B_66)),A_65)
      | r1_tarski(A_65,B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(A_25,k1_relat_1(C_27))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),k1_relat_1(A_69))
      | r1_tarski(A_69,B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_86,c_22])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_73,B_74,B_75] :
      ( r2_hidden('#skF_2'(A_73,B_74),B_75)
      | ~ r1_tarski(k1_relat_1(A_73),B_75)
      | r1_tarski(A_73,B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_303,plain,(
    ! [A_126,B_127,B_128,B_129] :
      ( r2_hidden('#skF_2'(A_126,B_127),B_128)
      | ~ r1_tarski(B_129,B_128)
      | ~ r1_tarski(k1_relat_1(A_126),B_129)
      | r1_tarski(A_126,B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_316,plain,(
    ! [A_130,B_131] :
      ( r2_hidden('#skF_2'(A_130,B_131),'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_130),k1_relat_1('#skF_5'))
      | r1_tarski(A_130,B_131)
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_319,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_2'('#skF_5',B_131),'#skF_4')
      | r1_tarski('#skF_5',B_131)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_316])).

tff(c_322,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_2'('#skF_5',B_131),'#skF_4')
      | r1_tarski('#skF_5',B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_319])).

tff(c_18,plain,(
    ! [A_8,B_18] :
      ( r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),A_8)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( r2_hidden(k4_tarski(A_103,B_104),k5_relat_1(k6_relat_1(C_105),D_106))
      | ~ r2_hidden(k4_tarski(A_103,B_104),D_106)
      | ~ r2_hidden(A_103,C_105)
      | ~ v1_relat_1(D_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_8,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),B_18)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_927,plain,(
    ! [A_293,C_294,D_295] :
      ( r1_tarski(A_293,k5_relat_1(k6_relat_1(C_294),D_295))
      | ~ v1_relat_1(A_293)
      | ~ r2_hidden(k4_tarski('#skF_2'(A_293,k5_relat_1(k6_relat_1(C_294),D_295)),'#skF_3'(A_293,k5_relat_1(k6_relat_1(C_294),D_295))),D_295)
      | ~ r2_hidden('#skF_2'(A_293,k5_relat_1(k6_relat_1(C_294),D_295)),C_294)
      | ~ v1_relat_1(D_295) ) ),
    inference(resolution,[status(thm)],[c_212,c_16])).

tff(c_958,plain,(
    ! [A_296,C_297] :
      ( ~ r2_hidden('#skF_2'(A_296,k5_relat_1(k6_relat_1(C_297),A_296)),C_297)
      | r1_tarski(A_296,k5_relat_1(k6_relat_1(C_297),A_296))
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_18,c_927])).

tff(c_982,plain,
    ( ~ v1_relat_1('#skF_5')
    | r1_tarski('#skF_5',k5_relat_1(k6_relat_1('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_322,c_958])).

tff(c_1004,plain,(
    r1_tarski('#skF_5',k5_relat_1(k6_relat_1('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_982])).

tff(c_30,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_32),B_33),B_33)
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

tff(c_186,plain,(
    ! [A_95,B_96,B_97,A_98] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_97)
      | ~ r1_tarski(A_95,k5_relat_1(k6_relat_1(A_98),B_97))
      | r1_tarski(A_95,B_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_30,c_126])).

tff(c_237,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(A_107),B_108),B_109),B_108)
      | r1_tarski(k5_relat_1(k6_relat_1(A_107),B_108),B_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_430,plain,(
    ! [A_199,B_200,B_201,B_202] :
      ( r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(A_199),B_200),B_201),B_202)
      | ~ r1_tarski(B_200,B_202)
      | r1_tarski(k5_relat_1(k6_relat_1(A_199),B_200),B_201)
      | ~ v1_relat_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_237,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_449,plain,(
    ! [B_207,B_208,A_209] :
      ( ~ r1_tarski(B_207,B_208)
      | r1_tarski(k5_relat_1(k6_relat_1(A_209),B_207),B_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_430,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_500,plain,(
    ! [A_209,B_207,B_208] :
      ( k5_relat_1(k6_relat_1(A_209),B_207) = B_208
      | ~ r1_tarski(B_208,k5_relat_1(k6_relat_1(A_209),B_207))
      | ~ r1_tarski(B_207,B_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_449,c_8])).

tff(c_1016,plain,
    ( k5_relat_1(k6_relat_1('#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1004,c_500])).

tff(c_1047,plain,(
    k5_relat_1(k6_relat_1('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12,c_1016])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.66  
% 3.82/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.66  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.82/1.66  
% 3.82/1.66  %Foreground sorts:
% 3.82/1.66  
% 3.82/1.66  
% 3.82/1.66  %Background operators:
% 3.82/1.66  
% 3.82/1.66  
% 3.82/1.66  %Foreground operators:
% 3.82/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.82/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.82/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.82/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.82/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.82/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.82/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.82/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.66  
% 4.04/1.68  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 4.04/1.68  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.04/1.68  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 4.04/1.68  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 4.04/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.04/1.68  tff(f_64, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 4.04/1.68  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 4.04/1.68  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.68  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.68  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.68  tff(c_36, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.68  tff(c_86, plain, (![A_65, B_66]: (r2_hidden(k4_tarski('#skF_2'(A_65, B_66), '#skF_3'(A_65, B_66)), A_65) | r1_tarski(A_65, B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.04/1.68  tff(c_22, plain, (![A_25, C_27, B_26]: (r2_hidden(A_25, k1_relat_1(C_27)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.04/1.68  tff(c_110, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), k1_relat_1(A_69)) | r1_tarski(A_69, B_70) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_86, c_22])).
% 4.04/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.68  tff(c_118, plain, (![A_73, B_74, B_75]: (r2_hidden('#skF_2'(A_73, B_74), B_75) | ~r1_tarski(k1_relat_1(A_73), B_75) | r1_tarski(A_73, B_74) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_110, c_2])).
% 4.04/1.68  tff(c_303, plain, (![A_126, B_127, B_128, B_129]: (r2_hidden('#skF_2'(A_126, B_127), B_128) | ~r1_tarski(B_129, B_128) | ~r1_tarski(k1_relat_1(A_126), B_129) | r1_tarski(A_126, B_127) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_118, c_2])).
% 4.04/1.68  tff(c_316, plain, (![A_130, B_131]: (r2_hidden('#skF_2'(A_130, B_131), '#skF_4') | ~r1_tarski(k1_relat_1(A_130), k1_relat_1('#skF_5')) | r1_tarski(A_130, B_131) | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_36, c_303])).
% 4.04/1.68  tff(c_319, plain, (![B_131]: (r2_hidden('#skF_2'('#skF_5', B_131), '#skF_4') | r1_tarski('#skF_5', B_131) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_316])).
% 4.04/1.68  tff(c_322, plain, (![B_131]: (r2_hidden('#skF_2'('#skF_5', B_131), '#skF_4') | r1_tarski('#skF_5', B_131))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_319])).
% 4.04/1.68  tff(c_18, plain, (![A_8, B_18]: (r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), A_8) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.04/1.68  tff(c_212, plain, (![A_103, B_104, C_105, D_106]: (r2_hidden(k4_tarski(A_103, B_104), k5_relat_1(k6_relat_1(C_105), D_106)) | ~r2_hidden(k4_tarski(A_103, B_104), D_106) | ~r2_hidden(A_103, C_105) | ~v1_relat_1(D_106))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.04/1.68  tff(c_16, plain, (![A_8, B_18]: (~r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), B_18) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.04/1.68  tff(c_927, plain, (![A_293, C_294, D_295]: (r1_tarski(A_293, k5_relat_1(k6_relat_1(C_294), D_295)) | ~v1_relat_1(A_293) | ~r2_hidden(k4_tarski('#skF_2'(A_293, k5_relat_1(k6_relat_1(C_294), D_295)), '#skF_3'(A_293, k5_relat_1(k6_relat_1(C_294), D_295))), D_295) | ~r2_hidden('#skF_2'(A_293, k5_relat_1(k6_relat_1(C_294), D_295)), C_294) | ~v1_relat_1(D_295))), inference(resolution, [status(thm)], [c_212, c_16])).
% 4.04/1.68  tff(c_958, plain, (![A_296, C_297]: (~r2_hidden('#skF_2'(A_296, k5_relat_1(k6_relat_1(C_297), A_296)), C_297) | r1_tarski(A_296, k5_relat_1(k6_relat_1(C_297), A_296)) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_18, c_927])).
% 4.04/1.68  tff(c_982, plain, (~v1_relat_1('#skF_5') | r1_tarski('#skF_5', k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_322, c_958])).
% 4.04/1.68  tff(c_1004, plain, (r1_tarski('#skF_5', k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_982])).
% 4.04/1.68  tff(c_30, plain, (![A_32, B_33]: (r1_tarski(k5_relat_1(k6_relat_1(A_32), B_33), B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.04/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.68  tff(c_68, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.68  tff(c_74, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_1'(A_54, B_55), B_56) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_6, c_68])).
% 4.04/1.68  tff(c_126, plain, (![A_79, B_80, B_81, B_82]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(B_82, B_81) | ~r1_tarski(A_79, B_82) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_74, c_2])).
% 4.04/1.68  tff(c_186, plain, (![A_95, B_96, B_97, A_98]: (r2_hidden('#skF_1'(A_95, B_96), B_97) | ~r1_tarski(A_95, k5_relat_1(k6_relat_1(A_98), B_97)) | r1_tarski(A_95, B_96) | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_30, c_126])).
% 4.04/1.68  tff(c_237, plain, (![A_107, B_108, B_109]: (r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(A_107), B_108), B_109), B_108) | r1_tarski(k5_relat_1(k6_relat_1(A_107), B_108), B_109) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_12, c_186])).
% 4.04/1.68  tff(c_430, plain, (![A_199, B_200, B_201, B_202]: (r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(A_199), B_200), B_201), B_202) | ~r1_tarski(B_200, B_202) | r1_tarski(k5_relat_1(k6_relat_1(A_199), B_200), B_201) | ~v1_relat_1(B_200))), inference(resolution, [status(thm)], [c_237, c_2])).
% 4.04/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.68  tff(c_449, plain, (![B_207, B_208, A_209]: (~r1_tarski(B_207, B_208) | r1_tarski(k5_relat_1(k6_relat_1(A_209), B_207), B_208) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_430, c_4])).
% 4.04/1.68  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.68  tff(c_500, plain, (![A_209, B_207, B_208]: (k5_relat_1(k6_relat_1(A_209), B_207)=B_208 | ~r1_tarski(B_208, k5_relat_1(k6_relat_1(A_209), B_207)) | ~r1_tarski(B_207, B_208) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_449, c_8])).
% 4.04/1.68  tff(c_1016, plain, (k5_relat_1(k6_relat_1('#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', '#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1004, c_500])).
% 4.04/1.68  tff(c_1047, plain, (k5_relat_1(k6_relat_1('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12, c_1016])).
% 4.04/1.68  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1047])).
% 4.04/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.68  
% 4.04/1.68  Inference rules
% 4.04/1.68  ----------------------
% 4.04/1.68  #Ref     : 0
% 4.04/1.68  #Sup     : 244
% 4.04/1.68  #Fact    : 0
% 4.04/1.68  #Define  : 0
% 4.04/1.68  #Split   : 3
% 4.04/1.68  #Chain   : 0
% 4.04/1.68  #Close   : 0
% 4.04/1.68  
% 4.04/1.68  Ordering : KBO
% 4.04/1.68  
% 4.04/1.68  Simplification rules
% 4.04/1.68  ----------------------
% 4.04/1.68  #Subsume      : 38
% 4.04/1.68  #Demod        : 13
% 4.04/1.68  #Tautology    : 12
% 4.04/1.68  #SimpNegUnit  : 1
% 4.04/1.68  #BackRed      : 0
% 4.04/1.68  
% 4.04/1.68  #Partial instantiations: 0
% 4.04/1.68  #Strategies tried      : 1
% 4.04/1.68  
% 4.04/1.68  Timing (in seconds)
% 4.04/1.68  ----------------------
% 4.04/1.68  Preprocessing        : 0.29
% 4.04/1.68  Parsing              : 0.16
% 4.04/1.68  CNF conversion       : 0.02
% 4.04/1.68  Main loop            : 0.60
% 4.04/1.68  Inferencing          : 0.20
% 4.04/1.68  Reduction            : 0.13
% 4.04/1.68  Demodulation         : 0.08
% 4.04/1.68  BG Simplification    : 0.02
% 4.04/1.68  Subsumption          : 0.21
% 4.04/1.68  Abstraction          : 0.02
% 4.04/1.68  MUC search           : 0.00
% 4.04/1.68  Cooper               : 0.00
% 4.04/1.68  Total                : 0.92
% 4.04/1.68  Index Insertion      : 0.00
% 4.04/1.68  Index Deletion       : 0.00
% 4.04/1.68  Index Matching       : 0.00
% 4.04/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
