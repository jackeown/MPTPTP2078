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
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.38s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 351 expanded)
%              Number of leaves         :   30 ( 131 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 706 expanded)
%              Number of equality atoms :   24 ( 104 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_11','#skF_13')
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77),B_77)
      | r2_hidden('#skF_3'(A_76,B_77),A_76)
      | B_77 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_52,C_53,B_54] :
      ( ~ r2_hidden(A_52,C_53)
      | ~ r1_xboole_0(k2_tarski(A_52,B_54),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_111,plain,(
    ! [B_77] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_77),B_77)
      | k1_xboole_0 = B_77 ) ),
    inference(resolution,[status(thm)],[c_98,c_62])).

tff(c_209,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden('#skF_9'(A_97,B_98,k2_zfmisc_1(A_97,B_98),D_99),B_98)
      | ~ r2_hidden(D_99,k2_zfmisc_1(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_218,plain,(
    ! [D_100,A_101] : ~ r2_hidden(D_100,k2_zfmisc_1(A_101,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_209,c_62])).

tff(c_259,plain,(
    ! [A_101] : k2_zfmisc_1(A_101,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_218])).

tff(c_624,plain,(
    ! [A_151,B_152,C_153] :
      ( r2_hidden('#skF_6'(A_151,B_152,C_153),B_152)
      | r2_hidden('#skF_7'(A_151,B_152,C_153),C_153)
      | k2_zfmisc_1(A_151,B_152) = C_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_630,plain,(
    ! [A_151,C_153] :
      ( r2_hidden('#skF_7'(A_151,k1_xboole_0,C_153),C_153)
      | k2_zfmisc_1(A_151,k1_xboole_0) = C_153 ) ),
    inference(resolution,[status(thm)],[c_624,c_62])).

tff(c_637,plain,(
    ! [A_151,C_153] :
      ( r2_hidden('#skF_7'(A_151,k1_xboole_0,C_153),C_153)
      | k1_xboole_0 = C_153 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_630])).

tff(c_54,plain,(
    r1_tarski(k2_zfmisc_1('#skF_10','#skF_11'),k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_187,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( r2_hidden(k4_tarski(A_90,B_91),k2_zfmisc_1(C_92,D_93))
      | ~ r2_hidden(B_91,D_93)
      | ~ r2_hidden(A_90,C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_854,plain,(
    ! [C_187,B_188,B_185,D_186,A_189] :
      ( r2_hidden(k4_tarski(A_189,B_185),B_188)
      | ~ r1_tarski(k2_zfmisc_1(C_187,D_186),B_188)
      | ~ r2_hidden(B_185,D_186)
      | ~ r2_hidden(A_189,C_187) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_870,plain,(
    ! [A_190,B_191] :
      ( r2_hidden(k4_tarski(A_190,B_191),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_191,'#skF_11')
      | ~ r2_hidden(A_190,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_54,c_854])).

tff(c_46,plain,(
    ! [A_44,C_46,B_45,D_47] :
      ( r2_hidden(A_44,C_46)
      | ~ r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_882,plain,(
    ! [A_190,B_191] :
      ( r2_hidden(A_190,'#skF_12')
      | ~ r2_hidden(B_191,'#skF_11')
      | ~ r2_hidden(A_190,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_870,c_46])).

tff(c_886,plain,(
    ! [B_192] : ~ r2_hidden(B_192,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_882])).

tff(c_992,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_637,c_886])).

tff(c_1032,plain,(
    ! [A_101] : k2_zfmisc_1(A_101,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_992,c_259])).

tff(c_52,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1040,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_52])).

tff(c_1089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_1040])).

tff(c_1091,plain,(
    ! [A_198] :
      ( r2_hidden(A_198,'#skF_12')
      | ~ r2_hidden(A_198,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_882])).

tff(c_1712,plain,(
    ! [B_222] :
      ( r2_hidden('#skF_1'('#skF_10',B_222),'#skF_12')
      | r1_tarski('#skF_10',B_222) ) ),
    inference(resolution,[status(thm)],[c_6,c_1091])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1718,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_1712,c_4])).

tff(c_1723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_1718])).

tff(c_1724,plain,(
    ~ r1_tarski('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1788,plain,(
    ! [A_253,B_254] :
      ( r2_hidden('#skF_2'(A_253,B_254),B_254)
      | r2_hidden('#skF_3'(A_253,B_254),A_253)
      | B_254 = A_253 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1726,plain,(
    ! [A_223,C_224,B_225] :
      ( ~ r2_hidden(A_223,C_224)
      | ~ r1_xboole_0(k2_tarski(A_223,B_225),C_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1731,plain,(
    ! [A_223] : ~ r2_hidden(A_223,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_1726])).

tff(c_1802,plain,(
    ! [B_254] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_254),B_254)
      | k1_xboole_0 = B_254 ) ),
    inference(resolution,[status(thm)],[c_1788,c_1731])).

tff(c_1868,plain,(
    ! [A_265,B_266,D_267] :
      ( r2_hidden('#skF_9'(A_265,B_266,k2_zfmisc_1(A_265,B_266),D_267),B_266)
      | ~ r2_hidden(D_267,k2_zfmisc_1(A_265,B_266)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1877,plain,(
    ! [D_268,A_269] : ~ r2_hidden(D_268,k2_zfmisc_1(A_269,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1868,c_1731])).

tff(c_1917,plain,(
    ! [A_269] : k2_zfmisc_1(A_269,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1802,c_1877])).

tff(c_2105,plain,(
    ! [A_286,B_287,C_288] :
      ( r2_hidden('#skF_6'(A_286,B_287,C_288),B_287)
      | r2_hidden('#skF_7'(A_286,B_287,C_288),C_288)
      | k2_zfmisc_1(A_286,B_287) = C_288 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2111,plain,(
    ! [A_286,C_288] :
      ( r2_hidden('#skF_7'(A_286,k1_xboole_0,C_288),C_288)
      | k2_zfmisc_1(A_286,k1_xboole_0) = C_288 ) ),
    inference(resolution,[status(thm)],[c_2105,c_1731])).

tff(c_2118,plain,(
    ! [A_286,C_288] :
      ( r2_hidden('#skF_7'(A_286,k1_xboole_0,C_288),C_288)
      | k1_xboole_0 = C_288 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1917,c_2111])).

tff(c_1856,plain,(
    ! [A_261,B_262,C_263,D_264] :
      ( r2_hidden(k4_tarski(A_261,B_262),k2_zfmisc_1(C_263,D_264))
      | ~ r2_hidden(B_262,D_264)
      | ~ r2_hidden(A_261,C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2652,plain,(
    ! [B_397,C_396,B_398,A_400,D_399] :
      ( r2_hidden(k4_tarski(A_400,B_397),B_398)
      | ~ r1_tarski(k2_zfmisc_1(C_396,D_399),B_398)
      | ~ r2_hidden(B_397,D_399)
      | ~ r2_hidden(A_400,C_396) ) ),
    inference(resolution,[status(thm)],[c_1856,c_2])).

tff(c_2668,plain,(
    ! [A_401,B_402] :
      ( r2_hidden(k4_tarski(A_401,B_402),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_402,'#skF_11')
      | ~ r2_hidden(A_401,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_54,c_2652])).

tff(c_44,plain,(
    ! [B_45,D_47,A_44,C_46] :
      ( r2_hidden(B_45,D_47)
      | ~ r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2683,plain,(
    ! [B_402,A_401] :
      ( r2_hidden(B_402,'#skF_13')
      | ~ r2_hidden(B_402,'#skF_11')
      | ~ r2_hidden(A_401,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2668,c_44])).

tff(c_2692,plain,(
    ! [A_408] : ~ r2_hidden(A_408,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2683])).

tff(c_2825,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2118,c_2692])).

tff(c_1948,plain,(
    ! [A_271,B_272,D_273] :
      ( r2_hidden('#skF_8'(A_271,B_272,k2_zfmisc_1(A_271,B_272),D_273),A_271)
      | ~ r2_hidden(D_273,k2_zfmisc_1(A_271,B_272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1961,plain,(
    ! [D_274,B_275] : ~ r2_hidden(D_274,k2_zfmisc_1(k1_xboole_0,B_275)) ),
    inference(resolution,[status(thm)],[c_1948,c_1731])).

tff(c_2009,plain,(
    ! [B_275] : k2_zfmisc_1(k1_xboole_0,B_275) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1802,c_1961])).

tff(c_2865,plain,(
    ! [B_275] : k2_zfmisc_1('#skF_10',B_275) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2825,c_2825,c_2009])).

tff(c_2873,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2825,c_52])).

tff(c_2920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2865,c_2873])).

tff(c_3126,plain,(
    ! [B_420] :
      ( r2_hidden(B_420,'#skF_13')
      | ~ r2_hidden(B_420,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_2683])).

tff(c_4470,plain,(
    ! [B_467] :
      ( r2_hidden('#skF_1'('#skF_11',B_467),'#skF_13')
      | r1_tarski('#skF_11',B_467) ) ),
    inference(resolution,[status(thm)],[c_6,c_3126])).

tff(c_4476,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_4470,c_4])).

tff(c_4481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1724,c_1724,c_4476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:19:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.00  
% 5.38/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_1 > #skF_12
% 5.38/2.00  
% 5.38/2.00  %Foreground sorts:
% 5.38/2.00  
% 5.38/2.00  
% 5.38/2.00  %Background operators:
% 5.38/2.00  
% 5.38/2.00  
% 5.38/2.00  %Foreground operators:
% 5.38/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.38/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.38/2.00  tff('#skF_11', type, '#skF_11': $i).
% 5.38/2.00  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.38/2.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.38/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.38/2.00  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 5.38/2.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.38/2.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.38/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.38/2.00  tff('#skF_10', type, '#skF_10': $i).
% 5.38/2.00  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.38/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.38/2.00  tff('#skF_13', type, '#skF_13': $i).
% 5.38/2.00  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.38/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.38/2.00  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.38/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.38/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.38/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.38/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.38/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.38/2.00  tff('#skF_12', type, '#skF_12': $i).
% 5.38/2.00  
% 5.38/2.02  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.38/2.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.38/2.02  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.38/2.02  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.38/2.02  tff(f_64, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 5.38/2.02  tff(f_53, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.38/2.02  tff(f_59, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.38/2.02  tff(c_50, plain, (~r1_tarski('#skF_11', '#skF_13') | ~r1_tarski('#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.38/2.02  tff(c_56, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_50])).
% 5.38/2.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.38/2.02  tff(c_98, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77), B_77) | r2_hidden('#skF_3'(A_76, B_77), A_76) | B_77=A_76)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.38/2.02  tff(c_16, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.38/2.02  tff(c_57, plain, (![A_52, C_53, B_54]: (~r2_hidden(A_52, C_53) | ~r1_xboole_0(k2_tarski(A_52, B_54), C_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.38/2.02  tff(c_62, plain, (![A_52]: (~r2_hidden(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_57])).
% 5.38/2.02  tff(c_111, plain, (![B_77]: (r2_hidden('#skF_2'(k1_xboole_0, B_77), B_77) | k1_xboole_0=B_77)), inference(resolution, [status(thm)], [c_98, c_62])).
% 5.38/2.02  tff(c_209, plain, (![A_97, B_98, D_99]: (r2_hidden('#skF_9'(A_97, B_98, k2_zfmisc_1(A_97, B_98), D_99), B_98) | ~r2_hidden(D_99, k2_zfmisc_1(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.38/2.02  tff(c_218, plain, (![D_100, A_101]: (~r2_hidden(D_100, k2_zfmisc_1(A_101, k1_xboole_0)))), inference(resolution, [status(thm)], [c_209, c_62])).
% 5.38/2.02  tff(c_259, plain, (![A_101]: (k2_zfmisc_1(A_101, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_218])).
% 5.38/2.02  tff(c_624, plain, (![A_151, B_152, C_153]: (r2_hidden('#skF_6'(A_151, B_152, C_153), B_152) | r2_hidden('#skF_7'(A_151, B_152, C_153), C_153) | k2_zfmisc_1(A_151, B_152)=C_153)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.38/2.02  tff(c_630, plain, (![A_151, C_153]: (r2_hidden('#skF_7'(A_151, k1_xboole_0, C_153), C_153) | k2_zfmisc_1(A_151, k1_xboole_0)=C_153)), inference(resolution, [status(thm)], [c_624, c_62])).
% 5.38/2.02  tff(c_637, plain, (![A_151, C_153]: (r2_hidden('#skF_7'(A_151, k1_xboole_0, C_153), C_153) | k1_xboole_0=C_153)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_630])).
% 5.38/2.02  tff(c_54, plain, (r1_tarski(k2_zfmisc_1('#skF_10', '#skF_11'), k2_zfmisc_1('#skF_12', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.38/2.02  tff(c_187, plain, (![A_90, B_91, C_92, D_93]: (r2_hidden(k4_tarski(A_90, B_91), k2_zfmisc_1(C_92, D_93)) | ~r2_hidden(B_91, D_93) | ~r2_hidden(A_90, C_92))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.38/2.02  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.38/2.02  tff(c_854, plain, (![C_187, B_188, B_185, D_186, A_189]: (r2_hidden(k4_tarski(A_189, B_185), B_188) | ~r1_tarski(k2_zfmisc_1(C_187, D_186), B_188) | ~r2_hidden(B_185, D_186) | ~r2_hidden(A_189, C_187))), inference(resolution, [status(thm)], [c_187, c_2])).
% 5.38/2.02  tff(c_870, plain, (![A_190, B_191]: (r2_hidden(k4_tarski(A_190, B_191), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_191, '#skF_11') | ~r2_hidden(A_190, '#skF_10'))), inference(resolution, [status(thm)], [c_54, c_854])).
% 5.38/2.02  tff(c_46, plain, (![A_44, C_46, B_45, D_47]: (r2_hidden(A_44, C_46) | ~r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.38/2.02  tff(c_882, plain, (![A_190, B_191]: (r2_hidden(A_190, '#skF_12') | ~r2_hidden(B_191, '#skF_11') | ~r2_hidden(A_190, '#skF_10'))), inference(resolution, [status(thm)], [c_870, c_46])).
% 5.38/2.02  tff(c_886, plain, (![B_192]: (~r2_hidden(B_192, '#skF_11'))), inference(splitLeft, [status(thm)], [c_882])).
% 5.38/2.02  tff(c_992, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_637, c_886])).
% 5.38/2.02  tff(c_1032, plain, (![A_101]: (k2_zfmisc_1(A_101, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_992, c_992, c_259])).
% 5.38/2.02  tff(c_52, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.38/2.02  tff(c_1040, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_992, c_52])).
% 5.38/2.02  tff(c_1089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1032, c_1040])).
% 5.38/2.02  tff(c_1091, plain, (![A_198]: (r2_hidden(A_198, '#skF_12') | ~r2_hidden(A_198, '#skF_10'))), inference(splitRight, [status(thm)], [c_882])).
% 5.38/2.02  tff(c_1712, plain, (![B_222]: (r2_hidden('#skF_1'('#skF_10', B_222), '#skF_12') | r1_tarski('#skF_10', B_222))), inference(resolution, [status(thm)], [c_6, c_1091])).
% 5.38/2.02  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.38/2.02  tff(c_1718, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_1712, c_4])).
% 5.38/2.02  tff(c_1723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_1718])).
% 5.38/2.02  tff(c_1724, plain, (~r1_tarski('#skF_11', '#skF_13')), inference(splitRight, [status(thm)], [c_50])).
% 5.38/2.02  tff(c_1788, plain, (![A_253, B_254]: (r2_hidden('#skF_2'(A_253, B_254), B_254) | r2_hidden('#skF_3'(A_253, B_254), A_253) | B_254=A_253)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.38/2.02  tff(c_1726, plain, (![A_223, C_224, B_225]: (~r2_hidden(A_223, C_224) | ~r1_xboole_0(k2_tarski(A_223, B_225), C_224))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.38/2.02  tff(c_1731, plain, (![A_223]: (~r2_hidden(A_223, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_1726])).
% 5.38/2.02  tff(c_1802, plain, (![B_254]: (r2_hidden('#skF_2'(k1_xboole_0, B_254), B_254) | k1_xboole_0=B_254)), inference(resolution, [status(thm)], [c_1788, c_1731])).
% 5.38/2.02  tff(c_1868, plain, (![A_265, B_266, D_267]: (r2_hidden('#skF_9'(A_265, B_266, k2_zfmisc_1(A_265, B_266), D_267), B_266) | ~r2_hidden(D_267, k2_zfmisc_1(A_265, B_266)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.38/2.02  tff(c_1877, plain, (![D_268, A_269]: (~r2_hidden(D_268, k2_zfmisc_1(A_269, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1868, c_1731])).
% 5.38/2.02  tff(c_1917, plain, (![A_269]: (k2_zfmisc_1(A_269, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1802, c_1877])).
% 5.38/2.02  tff(c_2105, plain, (![A_286, B_287, C_288]: (r2_hidden('#skF_6'(A_286, B_287, C_288), B_287) | r2_hidden('#skF_7'(A_286, B_287, C_288), C_288) | k2_zfmisc_1(A_286, B_287)=C_288)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.38/2.02  tff(c_2111, plain, (![A_286, C_288]: (r2_hidden('#skF_7'(A_286, k1_xboole_0, C_288), C_288) | k2_zfmisc_1(A_286, k1_xboole_0)=C_288)), inference(resolution, [status(thm)], [c_2105, c_1731])).
% 5.38/2.02  tff(c_2118, plain, (![A_286, C_288]: (r2_hidden('#skF_7'(A_286, k1_xboole_0, C_288), C_288) | k1_xboole_0=C_288)), inference(demodulation, [status(thm), theory('equality')], [c_1917, c_2111])).
% 5.38/2.02  tff(c_1856, plain, (![A_261, B_262, C_263, D_264]: (r2_hidden(k4_tarski(A_261, B_262), k2_zfmisc_1(C_263, D_264)) | ~r2_hidden(B_262, D_264) | ~r2_hidden(A_261, C_263))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.38/2.02  tff(c_2652, plain, (![B_397, C_396, B_398, A_400, D_399]: (r2_hidden(k4_tarski(A_400, B_397), B_398) | ~r1_tarski(k2_zfmisc_1(C_396, D_399), B_398) | ~r2_hidden(B_397, D_399) | ~r2_hidden(A_400, C_396))), inference(resolution, [status(thm)], [c_1856, c_2])).
% 5.38/2.02  tff(c_2668, plain, (![A_401, B_402]: (r2_hidden(k4_tarski(A_401, B_402), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_402, '#skF_11') | ~r2_hidden(A_401, '#skF_10'))), inference(resolution, [status(thm)], [c_54, c_2652])).
% 5.38/2.02  tff(c_44, plain, (![B_45, D_47, A_44, C_46]: (r2_hidden(B_45, D_47) | ~r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.38/2.02  tff(c_2683, plain, (![B_402, A_401]: (r2_hidden(B_402, '#skF_13') | ~r2_hidden(B_402, '#skF_11') | ~r2_hidden(A_401, '#skF_10'))), inference(resolution, [status(thm)], [c_2668, c_44])).
% 5.38/2.02  tff(c_2692, plain, (![A_408]: (~r2_hidden(A_408, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2683])).
% 5.38/2.02  tff(c_2825, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2118, c_2692])).
% 5.38/2.02  tff(c_1948, plain, (![A_271, B_272, D_273]: (r2_hidden('#skF_8'(A_271, B_272, k2_zfmisc_1(A_271, B_272), D_273), A_271) | ~r2_hidden(D_273, k2_zfmisc_1(A_271, B_272)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.38/2.02  tff(c_1961, plain, (![D_274, B_275]: (~r2_hidden(D_274, k2_zfmisc_1(k1_xboole_0, B_275)))), inference(resolution, [status(thm)], [c_1948, c_1731])).
% 5.38/2.02  tff(c_2009, plain, (![B_275]: (k2_zfmisc_1(k1_xboole_0, B_275)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1802, c_1961])).
% 5.38/2.02  tff(c_2865, plain, (![B_275]: (k2_zfmisc_1('#skF_10', B_275)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2825, c_2825, c_2009])).
% 5.38/2.02  tff(c_2873, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2825, c_52])).
% 5.38/2.02  tff(c_2920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2865, c_2873])).
% 5.38/2.02  tff(c_3126, plain, (![B_420]: (r2_hidden(B_420, '#skF_13') | ~r2_hidden(B_420, '#skF_11'))), inference(splitRight, [status(thm)], [c_2683])).
% 5.38/2.02  tff(c_4470, plain, (![B_467]: (r2_hidden('#skF_1'('#skF_11', B_467), '#skF_13') | r1_tarski('#skF_11', B_467))), inference(resolution, [status(thm)], [c_6, c_3126])).
% 5.38/2.02  tff(c_4476, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_4470, c_4])).
% 5.38/2.02  tff(c_4481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1724, c_1724, c_4476])).
% 5.38/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.02  
% 5.38/2.02  Inference rules
% 5.38/2.02  ----------------------
% 5.38/2.02  #Ref     : 0
% 5.38/2.02  #Sup     : 849
% 5.38/2.02  #Fact    : 0
% 5.38/2.02  #Define  : 0
% 5.38/2.02  #Split   : 12
% 5.38/2.02  #Chain   : 0
% 5.38/2.02  #Close   : 0
% 5.38/2.02  
% 5.38/2.02  Ordering : KBO
% 5.38/2.02  
% 5.38/2.02  Simplification rules
% 5.38/2.02  ----------------------
% 5.38/2.02  #Subsume      : 213
% 5.38/2.02  #Demod        : 602
% 5.38/2.02  #Tautology    : 128
% 5.38/2.02  #SimpNegUnit  : 32
% 5.38/2.02  #BackRed      : 268
% 5.38/2.02  
% 5.38/2.02  #Partial instantiations: 0
% 5.38/2.02  #Strategies tried      : 1
% 5.38/2.02  
% 5.38/2.02  Timing (in seconds)
% 5.38/2.02  ----------------------
% 5.38/2.02  Preprocessing        : 0.29
% 5.38/2.02  Parsing              : 0.15
% 5.38/2.02  CNF conversion       : 0.03
% 5.38/2.02  Main loop            : 0.95
% 5.38/2.02  Inferencing          : 0.33
% 5.38/2.02  Reduction            : 0.27
% 5.38/2.02  Demodulation         : 0.18
% 5.38/2.02  BG Simplification    : 0.04
% 5.38/2.02  Subsumption          : 0.23
% 5.38/2.02  Abstraction          : 0.04
% 5.38/2.02  MUC search           : 0.00
% 5.38/2.02  Cooper               : 0.00
% 5.38/2.02  Total                : 1.27
% 5.38/2.02  Index Insertion      : 0.00
% 5.38/2.02  Index Deletion       : 0.00
% 5.38/2.02  Index Matching       : 0.00
% 5.38/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
