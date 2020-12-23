%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 160 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 334 expanded)
%              Number of equality atoms :   34 ( 134 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_56,plain,
    ( k1_mcart_1('#skF_6') != '#skF_8'
    | k2_mcart_1('#skF_6') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_80,plain,(
    k2_mcart_1('#skF_6') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( k1_mcart_1('#skF_6') != '#skF_8'
    | k2_mcart_1('#skF_6') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_73,plain,(
    k2_mcart_1('#skF_6') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_28,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    r2_hidden('#skF_6',k2_zfmisc_1(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_158,plain,(
    ! [A_61,C_62,B_63] :
      ( r2_hidden(k2_mcart_1(A_61),C_62)
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_165,plain,(
    r2_hidden(k2_mcart_1('#skF_6'),k2_tarski('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_54,c_158])).

tff(c_421,plain,(
    ! [C_106,A_107,B_108] :
      ( k4_xboole_0(C_106,k2_tarski(A_107,B_108)) = C_106
      | r2_hidden(B_108,C_106)
      | r2_hidden(A_107,C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12613,plain,(
    ! [D_4335,A_4336,B_4337,C_4338] :
      ( ~ r2_hidden(D_4335,k2_tarski(A_4336,B_4337))
      | ~ r2_hidden(D_4335,C_4338)
      | r2_hidden(B_4337,C_4338)
      | r2_hidden(A_4336,C_4338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_10])).

tff(c_12688,plain,(
    ! [C_4339] :
      ( ~ r2_hidden(k2_mcart_1('#skF_6'),C_4339)
      | r2_hidden('#skF_10',C_4339)
      | r2_hidden('#skF_9',C_4339) ) ),
    inference(resolution,[status(thm)],[c_165,c_12613])).

tff(c_12717,plain,
    ( r2_hidden('#skF_10',k1_tarski(k2_mcart_1('#skF_6')))
    | r2_hidden('#skF_9',k1_tarski(k2_mcart_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_28,c_12688])).

tff(c_12748,plain,(
    r2_hidden('#skF_9',k1_tarski(k2_mcart_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_12717])).

tff(c_26,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12754,plain,(
    k2_mcart_1('#skF_6') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_12748,c_26])).

tff(c_12759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_12754])).

tff(c_12760,plain,(
    r2_hidden('#skF_10',k1_tarski(k2_mcart_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_12717])).

tff(c_12769,plain,(
    k2_mcart_1('#skF_6') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12760,c_26])).

tff(c_12776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_12769])).

tff(c_12777,plain,(
    k1_mcart_1('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12778,plain,(
    k2_mcart_1('#skF_6') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( k1_mcart_1('#skF_6') != '#skF_7'
    | k2_mcart_1('#skF_6') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12785,plain,(
    k1_mcart_1('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12778,c_58])).

tff(c_12881,plain,(
    ! [A_4372,B_4373,C_4374] :
      ( r2_hidden(k1_mcart_1(A_4372),B_4373)
      | ~ r2_hidden(A_4372,k2_zfmisc_1(B_4373,C_4374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12888,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_54,c_12881])).

tff(c_13044,plain,(
    ! [C_4400,A_4401,B_4402] :
      ( k4_xboole_0(C_4400,k2_tarski(A_4401,B_4402)) = C_4400
      | r2_hidden(B_4402,C_4400)
      | r2_hidden(A_4401,C_4400) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24365,plain,(
    ! [D_8031,A_8032,B_8033,C_8034] :
      ( ~ r2_hidden(D_8031,k2_tarski(A_8032,B_8033))
      | ~ r2_hidden(D_8031,C_8034)
      | r2_hidden(B_8033,C_8034)
      | r2_hidden(A_8032,C_8034) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13044,c_10])).

tff(c_24441,plain,(
    ! [C_8035] :
      ( ~ r2_hidden(k1_mcart_1('#skF_6'),C_8035)
      | r2_hidden('#skF_8',C_8035)
      | r2_hidden('#skF_7',C_8035) ) ),
    inference(resolution,[status(thm)],[c_12888,c_24365])).

tff(c_24470,plain,
    ( r2_hidden('#skF_8',k1_tarski(k1_mcart_1('#skF_6')))
    | r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_28,c_24441])).

tff(c_24471,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_24470])).

tff(c_24479,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_24471,c_26])).

tff(c_24486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12785,c_24479])).

tff(c_24487,plain,(
    r2_hidden('#skF_8',k1_tarski(k1_mcart_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_24470])).

tff(c_24494,plain,(
    k1_mcart_1('#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_24487,c_26])).

tff(c_24499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12777,c_24494])).

tff(c_24500,plain,(
    k1_mcart_1('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_24501,plain,(
    k2_mcart_1('#skF_6') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_6') != '#skF_7'
    | k2_mcart_1('#skF_6') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24515,plain,(
    k1_mcart_1('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24501,c_62])).

tff(c_24581,plain,(
    ! [A_8061,B_8062,C_8063] :
      ( r2_hidden(k1_mcart_1(A_8061),B_8062)
      | ~ r2_hidden(A_8061,k2_zfmisc_1(B_8062,C_8063)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24588,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_54,c_24581])).

tff(c_24769,plain,(
    ! [C_8095,A_8096,B_8097] :
      ( k4_xboole_0(C_8095,k2_tarski(A_8096,B_8097)) = C_8095
      | r2_hidden(B_8097,C_8095)
      | r2_hidden(A_8096,C_8095) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37206,plain,(
    ! [D_12104,A_12105,B_12106,C_12107] :
      ( ~ r2_hidden(D_12104,k2_tarski(A_12105,B_12106))
      | ~ r2_hidden(D_12104,C_12107)
      | r2_hidden(B_12106,C_12107)
      | r2_hidden(A_12105,C_12107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24769,c_10])).

tff(c_37280,plain,(
    ! [C_12108] :
      ( ~ r2_hidden(k1_mcart_1('#skF_6'),C_12108)
      | r2_hidden('#skF_8',C_12108)
      | r2_hidden('#skF_7',C_12108) ) ),
    inference(resolution,[status(thm)],[c_24588,c_37206])).

tff(c_37324,plain,
    ( r2_hidden('#skF_8',k1_tarski(k1_mcart_1('#skF_6')))
    | r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_28,c_37280])).

tff(c_37325,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_37324])).

tff(c_37337,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_37325,c_26])).

tff(c_37347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24515,c_37337])).

tff(c_37348,plain,(
    r2_hidden('#skF_8',k1_tarski(k1_mcart_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_37324])).

tff(c_37357,plain,(
    k1_mcart_1('#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_37348,c_26])).

tff(c_37363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24500,c_37357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.57/3.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/3.85  
% 10.57/3.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/3.86  %$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 10.57/3.86  
% 10.57/3.86  %Foreground sorts:
% 10.57/3.86  
% 10.57/3.86  
% 10.57/3.86  %Background operators:
% 10.57/3.86  
% 10.57/3.86  
% 10.57/3.86  %Foreground operators:
% 10.57/3.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.57/3.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.57/3.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.57/3.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.57/3.86  tff('#skF_7', type, '#skF_7': $i).
% 10.57/3.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.57/3.86  tff('#skF_10', type, '#skF_10': $i).
% 10.57/3.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.57/3.86  tff('#skF_6', type, '#skF_6': $i).
% 10.57/3.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.57/3.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.57/3.86  tff('#skF_9', type, '#skF_9': $i).
% 10.57/3.86  tff('#skF_8', type, '#skF_8': $i).
% 10.57/3.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.57/3.86  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.57/3.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.57/3.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.57/3.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.57/3.86  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.57/3.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.57/3.86  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.57/3.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.57/3.86  
% 10.57/3.87  tff(f_86, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 10.57/3.87  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.57/3.87  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 10.57/3.87  tff(f_63, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 10.57/3.87  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.57/3.87  tff(c_56, plain, (k1_mcart_1('#skF_6')!='#skF_8' | k2_mcart_1('#skF_6')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.57/3.87  tff(c_80, plain, (k2_mcart_1('#skF_6')!='#skF_10'), inference(splitLeft, [status(thm)], [c_56])).
% 10.57/3.87  tff(c_60, plain, (k1_mcart_1('#skF_6')!='#skF_8' | k2_mcart_1('#skF_6')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.57/3.87  tff(c_73, plain, (k2_mcart_1('#skF_6')!='#skF_9'), inference(splitLeft, [status(thm)], [c_60])).
% 10.57/3.87  tff(c_28, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.57/3.87  tff(c_54, plain, (r2_hidden('#skF_6', k2_zfmisc_1(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.57/3.87  tff(c_158, plain, (![A_61, C_62, B_63]: (r2_hidden(k2_mcart_1(A_61), C_62) | ~r2_hidden(A_61, k2_zfmisc_1(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.57/3.87  tff(c_165, plain, (r2_hidden(k2_mcart_1('#skF_6'), k2_tarski('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_54, c_158])).
% 10.57/3.87  tff(c_421, plain, (![C_106, A_107, B_108]: (k4_xboole_0(C_106, k2_tarski(A_107, B_108))=C_106 | r2_hidden(B_108, C_106) | r2_hidden(A_107, C_106))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.57/3.87  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.57/3.87  tff(c_12613, plain, (![D_4335, A_4336, B_4337, C_4338]: (~r2_hidden(D_4335, k2_tarski(A_4336, B_4337)) | ~r2_hidden(D_4335, C_4338) | r2_hidden(B_4337, C_4338) | r2_hidden(A_4336, C_4338))), inference(superposition, [status(thm), theory('equality')], [c_421, c_10])).
% 10.57/3.87  tff(c_12688, plain, (![C_4339]: (~r2_hidden(k2_mcart_1('#skF_6'), C_4339) | r2_hidden('#skF_10', C_4339) | r2_hidden('#skF_9', C_4339))), inference(resolution, [status(thm)], [c_165, c_12613])).
% 10.57/3.87  tff(c_12717, plain, (r2_hidden('#skF_10', k1_tarski(k2_mcart_1('#skF_6'))) | r2_hidden('#skF_9', k1_tarski(k2_mcart_1('#skF_6')))), inference(resolution, [status(thm)], [c_28, c_12688])).
% 10.57/3.87  tff(c_12748, plain, (r2_hidden('#skF_9', k1_tarski(k2_mcart_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_12717])).
% 10.57/3.87  tff(c_26, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.57/3.87  tff(c_12754, plain, (k2_mcart_1('#skF_6')='#skF_9'), inference(resolution, [status(thm)], [c_12748, c_26])).
% 10.57/3.87  tff(c_12759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_12754])).
% 10.57/3.87  tff(c_12760, plain, (r2_hidden('#skF_10', k1_tarski(k2_mcart_1('#skF_6')))), inference(splitRight, [status(thm)], [c_12717])).
% 10.57/3.87  tff(c_12769, plain, (k2_mcart_1('#skF_6')='#skF_10'), inference(resolution, [status(thm)], [c_12760, c_26])).
% 10.57/3.87  tff(c_12776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_12769])).
% 10.57/3.87  tff(c_12777, plain, (k1_mcart_1('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 10.57/3.87  tff(c_12778, plain, (k2_mcart_1('#skF_6')='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 10.57/3.87  tff(c_58, plain, (k1_mcart_1('#skF_6')!='#skF_7' | k2_mcart_1('#skF_6')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.57/3.87  tff(c_12785, plain, (k1_mcart_1('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12778, c_58])).
% 10.57/3.87  tff(c_12881, plain, (![A_4372, B_4373, C_4374]: (r2_hidden(k1_mcart_1(A_4372), B_4373) | ~r2_hidden(A_4372, k2_zfmisc_1(B_4373, C_4374)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.57/3.87  tff(c_12888, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_54, c_12881])).
% 10.57/3.87  tff(c_13044, plain, (![C_4400, A_4401, B_4402]: (k4_xboole_0(C_4400, k2_tarski(A_4401, B_4402))=C_4400 | r2_hidden(B_4402, C_4400) | r2_hidden(A_4401, C_4400))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.57/3.87  tff(c_24365, plain, (![D_8031, A_8032, B_8033, C_8034]: (~r2_hidden(D_8031, k2_tarski(A_8032, B_8033)) | ~r2_hidden(D_8031, C_8034) | r2_hidden(B_8033, C_8034) | r2_hidden(A_8032, C_8034))), inference(superposition, [status(thm), theory('equality')], [c_13044, c_10])).
% 10.57/3.87  tff(c_24441, plain, (![C_8035]: (~r2_hidden(k1_mcart_1('#skF_6'), C_8035) | r2_hidden('#skF_8', C_8035) | r2_hidden('#skF_7', C_8035))), inference(resolution, [status(thm)], [c_12888, c_24365])).
% 10.57/3.87  tff(c_24470, plain, (r2_hidden('#skF_8', k1_tarski(k1_mcart_1('#skF_6'))) | r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_6')))), inference(resolution, [status(thm)], [c_28, c_24441])).
% 10.57/3.87  tff(c_24471, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_24470])).
% 10.57/3.87  tff(c_24479, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_24471, c_26])).
% 10.57/3.87  tff(c_24486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12785, c_24479])).
% 10.57/3.87  tff(c_24487, plain, (r2_hidden('#skF_8', k1_tarski(k1_mcart_1('#skF_6')))), inference(splitRight, [status(thm)], [c_24470])).
% 10.57/3.87  tff(c_24494, plain, (k1_mcart_1('#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_24487, c_26])).
% 10.57/3.87  tff(c_24499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12777, c_24494])).
% 10.57/3.87  tff(c_24500, plain, (k1_mcart_1('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 10.57/3.87  tff(c_24501, plain, (k2_mcart_1('#skF_6')='#skF_9'), inference(splitRight, [status(thm)], [c_60])).
% 10.57/3.87  tff(c_62, plain, (k1_mcart_1('#skF_6')!='#skF_7' | k2_mcart_1('#skF_6')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.57/3.87  tff(c_24515, plain, (k1_mcart_1('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_24501, c_62])).
% 10.57/3.87  tff(c_24581, plain, (![A_8061, B_8062, C_8063]: (r2_hidden(k1_mcart_1(A_8061), B_8062) | ~r2_hidden(A_8061, k2_zfmisc_1(B_8062, C_8063)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.57/3.87  tff(c_24588, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_54, c_24581])).
% 10.57/3.87  tff(c_24769, plain, (![C_8095, A_8096, B_8097]: (k4_xboole_0(C_8095, k2_tarski(A_8096, B_8097))=C_8095 | r2_hidden(B_8097, C_8095) | r2_hidden(A_8096, C_8095))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.57/3.87  tff(c_37206, plain, (![D_12104, A_12105, B_12106, C_12107]: (~r2_hidden(D_12104, k2_tarski(A_12105, B_12106)) | ~r2_hidden(D_12104, C_12107) | r2_hidden(B_12106, C_12107) | r2_hidden(A_12105, C_12107))), inference(superposition, [status(thm), theory('equality')], [c_24769, c_10])).
% 10.57/3.87  tff(c_37280, plain, (![C_12108]: (~r2_hidden(k1_mcart_1('#skF_6'), C_12108) | r2_hidden('#skF_8', C_12108) | r2_hidden('#skF_7', C_12108))), inference(resolution, [status(thm)], [c_24588, c_37206])).
% 10.57/3.87  tff(c_37324, plain, (r2_hidden('#skF_8', k1_tarski(k1_mcart_1('#skF_6'))) | r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_6')))), inference(resolution, [status(thm)], [c_28, c_37280])).
% 10.57/3.87  tff(c_37325, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_37324])).
% 10.57/3.87  tff(c_37337, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_37325, c_26])).
% 10.57/3.87  tff(c_37347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24515, c_37337])).
% 10.57/3.87  tff(c_37348, plain, (r2_hidden('#skF_8', k1_tarski(k1_mcart_1('#skF_6')))), inference(splitRight, [status(thm)], [c_37324])).
% 10.57/3.87  tff(c_37357, plain, (k1_mcart_1('#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_37348, c_26])).
% 10.57/3.87  tff(c_37363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24500, c_37357])).
% 10.57/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/3.87  
% 10.57/3.87  Inference rules
% 10.57/3.87  ----------------------
% 10.57/3.87  #Ref     : 0
% 10.57/3.87  #Sup     : 6424
% 10.57/3.87  #Fact    : 6
% 10.57/3.87  #Define  : 0
% 10.57/3.87  #Split   : 14
% 10.57/3.87  #Chain   : 0
% 10.57/3.87  #Close   : 0
% 10.57/3.87  
% 10.57/3.87  Ordering : KBO
% 10.57/3.87  
% 10.57/3.87  Simplification rules
% 10.57/3.87  ----------------------
% 10.57/3.87  #Subsume      : 1330
% 10.57/3.87  #Demod        : 528
% 10.57/3.87  #Tautology    : 390
% 10.57/3.87  #SimpNegUnit  : 9
% 10.57/3.87  #BackRed      : 1
% 10.57/3.87  
% 10.57/3.87  #Partial instantiations: 8126
% 10.57/3.87  #Strategies tried      : 1
% 10.57/3.87  
% 10.57/3.87  Timing (in seconds)
% 10.57/3.87  ----------------------
% 10.74/3.87  Preprocessing        : 0.31
% 10.74/3.87  Parsing              : 0.16
% 10.74/3.87  CNF conversion       : 0.02
% 10.74/3.87  Main loop            : 2.80
% 10.74/3.87  Inferencing          : 1.08
% 10.74/3.87  Reduction            : 0.67
% 10.74/3.87  Demodulation         : 0.45
% 10.74/3.87  BG Simplification    : 0.17
% 10.74/3.87  Subsumption          : 0.70
% 10.74/3.87  Abstraction          : 0.22
% 10.74/3.87  MUC search           : 0.00
% 10.74/3.88  Cooper               : 0.00
% 10.74/3.88  Total                : 3.14
% 10.74/3.88  Index Insertion      : 0.00
% 10.74/3.88  Index Deletion       : 0.00
% 10.74/3.88  Index Matching       : 0.00
% 10.74/3.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
