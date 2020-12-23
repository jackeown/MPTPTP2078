%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 20.41s
% Output     : CNFRefutation 20.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 105 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 181 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_77,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_52,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_40,plain,(
    ! [B_36] : r2_hidden(B_36,k1_ordinal1(B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,(
    ! [B_47,A_48] :
      ( ~ r1_tarski(B_47,A_48)
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_70,plain,(
    ! [B_36] : ~ r1_tarski(k1_ordinal1(B_36),B_36) ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_352,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | r2_hidden(A_101,B_100)
      | ~ r2_hidden(A_101,k1_ordinal1(B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2741,plain,(
    ! [B_279,B_280] :
      ( '#skF_1'(k1_ordinal1(B_279),B_280) = B_279
      | r2_hidden('#skF_1'(k1_ordinal1(B_279),B_280),B_279)
      | r1_tarski(k1_ordinal1(B_279),B_280) ) ),
    inference(resolution,[status(thm)],[c_8,c_352])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2766,plain,(
    ! [B_279] :
      ( '#skF_1'(k1_ordinal1(B_279),B_279) = B_279
      | r1_tarski(k1_ordinal1(B_279),B_279) ) ),
    inference(resolution,[status(thm)],[c_2741,c_6])).

tff(c_2782,plain,(
    ! [B_281] : '#skF_1'(k1_ordinal1(B_281),B_281) = B_281 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_2766])).

tff(c_2801,plain,(
    ! [B_281] :
      ( ~ r2_hidden(B_281,B_281)
      | r1_tarski(k1_ordinal1(B_281),B_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2782,c_6])).

tff(c_2814,plain,(
    ! [B_281] : ~ r2_hidden(B_281,B_281) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2801])).

tff(c_50,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_89,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_36,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_tarski(A_34)) = k1_ordinal1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_129,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(B_55,A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_22])).

tff(c_138,plain,(
    ! [A_34] : r1_tarski(k1_tarski(A_34),k1_ordinal1(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_129])).

tff(c_52,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_383,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden(k1_mcart_1(A_103),B_104)
      | ~ r2_hidden(A_103,k2_zfmisc_1(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_398,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_383])).

tff(c_432,plain,(
    ! [C_112,B_113,A_114] :
      ( r2_hidden(C_112,B_113)
      | ~ r2_hidden(C_112,A_114)
      | ~ r1_tarski(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_647,plain,(
    ! [B_135] :
      ( r2_hidden(k1_mcart_1('#skF_3'),B_135)
      | ~ r1_tarski(k1_tarski('#skF_4'),B_135) ) ),
    inference(resolution,[status(thm)],[c_398,c_432])).

tff(c_38,plain,(
    ! [B_36,A_35] :
      ( B_36 = A_35
      | r2_hidden(A_35,B_36)
      | ~ r2_hidden(A_35,k1_ordinal1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42029,plain,(
    ! [B_1766] :
      ( k1_mcart_1('#skF_3') = B_1766
      | r2_hidden(k1_mcart_1('#skF_3'),B_1766)
      | ~ r1_tarski(k1_tarski('#skF_4'),k1_ordinal1(B_1766)) ) ),
    inference(resolution,[status(thm)],[c_647,c_38])).

tff(c_42067,plain,
    ( k1_mcart_1('#skF_3') = '#skF_4'
    | r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_42029])).

tff(c_42090,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_42067])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_314,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,B_90)
      | ~ r2_hidden(C_91,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1084,plain,(
    ! [C_177,B_178,A_179] :
      ( ~ r2_hidden(C_177,B_178)
      | ~ r2_hidden(C_177,k1_tarski(A_179))
      | r2_hidden(A_179,B_178) ) ),
    inference(resolution,[status(thm)],[c_34,c_314])).

tff(c_4293,plain,(
    ! [A_359,B_360,A_361] :
      ( ~ r2_hidden('#skF_2'(A_359,B_360),k1_tarski(A_361))
      | r2_hidden(A_361,A_359)
      | r1_xboole_0(A_359,B_360) ) ),
    inference(resolution,[status(thm)],[c_14,c_1084])).

tff(c_4324,plain,(
    ! [A_362,A_363] :
      ( r2_hidden(A_362,A_363)
      | r1_xboole_0(A_363,k1_tarski(A_362)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4293])).

tff(c_10,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,B_9)
      | ~ r2_hidden(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_33399,plain,(
    ! [C_1540,A_1541,A_1542] :
      ( ~ r2_hidden(C_1540,k1_tarski(A_1541))
      | ~ r2_hidden(C_1540,A_1542)
      | r2_hidden(A_1541,A_1542) ) ),
    inference(resolution,[status(thm)],[c_4324,c_10])).

tff(c_33663,plain,(
    ! [A_1542] :
      ( ~ r2_hidden(k1_mcart_1('#skF_3'),A_1542)
      | r2_hidden('#skF_4',A_1542) ) ),
    inference(resolution,[status(thm)],[c_398,c_33399])).

tff(c_42095,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42090,c_33663])).

tff(c_42109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2814,c_42095])).

tff(c_42110,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_42405,plain,(
    ! [A_1815,C_1816,B_1817] :
      ( r2_hidden(k2_mcart_1(A_1815),C_1816)
      | ~ r2_hidden(A_1815,k2_zfmisc_1(B_1817,C_1816)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42416,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_42405])).

tff(c_42423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42110,c_42416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.41/11.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.41/11.55  
% 20.41/11.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.41/11.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 20.41/11.56  
% 20.41/11.56  %Foreground sorts:
% 20.41/11.56  
% 20.41/11.56  
% 20.41/11.56  %Background operators:
% 20.41/11.56  
% 20.41/11.56  
% 20.41/11.56  %Foreground operators:
% 20.41/11.56  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 20.41/11.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.41/11.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.41/11.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.41/11.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.41/11.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.41/11.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.41/11.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.41/11.56  tff('#skF_5', type, '#skF_5': $i).
% 20.41/11.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.41/11.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 20.41/11.56  tff('#skF_3', type, '#skF_3': $i).
% 20.41/11.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.41/11.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.41/11.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 20.41/11.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.41/11.56  tff('#skF_4', type, '#skF_4': $i).
% 20.41/11.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.41/11.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.41/11.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 20.41/11.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.41/11.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.41/11.56  
% 20.41/11.57  tff(f_83, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 20.41/11.57  tff(f_88, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 20.41/11.57  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.41/11.57  tff(f_101, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 20.41/11.57  tff(f_77, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 20.41/11.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 20.41/11.57  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.41/11.57  tff(f_94, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 20.41/11.57  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 20.41/11.57  tff(f_75, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 20.41/11.57  tff(c_40, plain, (![B_36]: (r2_hidden(B_36, k1_ordinal1(B_36)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 20.41/11.57  tff(c_66, plain, (![B_47, A_48]: (~r1_tarski(B_47, A_48) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.41/11.57  tff(c_70, plain, (![B_36]: (~r1_tarski(k1_ordinal1(B_36), B_36))), inference(resolution, [status(thm)], [c_40, c_66])).
% 20.41/11.57  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.41/11.57  tff(c_352, plain, (![B_100, A_101]: (B_100=A_101 | r2_hidden(A_101, B_100) | ~r2_hidden(A_101, k1_ordinal1(B_100)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 20.41/11.57  tff(c_2741, plain, (![B_279, B_280]: ('#skF_1'(k1_ordinal1(B_279), B_280)=B_279 | r2_hidden('#skF_1'(k1_ordinal1(B_279), B_280), B_279) | r1_tarski(k1_ordinal1(B_279), B_280))), inference(resolution, [status(thm)], [c_8, c_352])).
% 20.41/11.57  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.41/11.57  tff(c_2766, plain, (![B_279]: ('#skF_1'(k1_ordinal1(B_279), B_279)=B_279 | r1_tarski(k1_ordinal1(B_279), B_279))), inference(resolution, [status(thm)], [c_2741, c_6])).
% 20.41/11.57  tff(c_2782, plain, (![B_281]: ('#skF_1'(k1_ordinal1(B_281), B_281)=B_281)), inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_2766])).
% 20.41/11.57  tff(c_2801, plain, (![B_281]: (~r2_hidden(B_281, B_281) | r1_tarski(k1_ordinal1(B_281), B_281))), inference(superposition, [status(thm), theory('equality')], [c_2782, c_6])).
% 20.41/11.57  tff(c_2814, plain, (![B_281]: (~r2_hidden(B_281, B_281))), inference(negUnitSimplification, [status(thm)], [c_70, c_2801])).
% 20.41/11.57  tff(c_50, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.41/11.57  tff(c_89, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 20.41/11.57  tff(c_36, plain, (![A_34]: (k2_xboole_0(A_34, k1_tarski(A_34))=k1_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.41/11.57  tff(c_90, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.41/11.57  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.41/11.57  tff(c_129, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(B_55, A_54)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_22])).
% 20.41/11.57  tff(c_138, plain, (![A_34]: (r1_tarski(k1_tarski(A_34), k1_ordinal1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_129])).
% 20.41/11.57  tff(c_52, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.41/11.57  tff(c_383, plain, (![A_103, B_104, C_105]: (r2_hidden(k1_mcart_1(A_103), B_104) | ~r2_hidden(A_103, k2_zfmisc_1(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.41/11.57  tff(c_398, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_383])).
% 20.41/11.57  tff(c_432, plain, (![C_112, B_113, A_114]: (r2_hidden(C_112, B_113) | ~r2_hidden(C_112, A_114) | ~r1_tarski(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.41/11.57  tff(c_647, plain, (![B_135]: (r2_hidden(k1_mcart_1('#skF_3'), B_135) | ~r1_tarski(k1_tarski('#skF_4'), B_135))), inference(resolution, [status(thm)], [c_398, c_432])).
% 20.41/11.57  tff(c_38, plain, (![B_36, A_35]: (B_36=A_35 | r2_hidden(A_35, B_36) | ~r2_hidden(A_35, k1_ordinal1(B_36)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 20.41/11.57  tff(c_42029, plain, (![B_1766]: (k1_mcart_1('#skF_3')=B_1766 | r2_hidden(k1_mcart_1('#skF_3'), B_1766) | ~r1_tarski(k1_tarski('#skF_4'), k1_ordinal1(B_1766)))), inference(resolution, [status(thm)], [c_647, c_38])).
% 20.41/11.57  tff(c_42067, plain, (k1_mcart_1('#skF_3')='#skF_4' | r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_138, c_42029])).
% 20.41/11.57  tff(c_42090, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_89, c_42067])).
% 20.41/11.57  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.41/11.57  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.41/11.57  tff(c_34, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.41/11.57  tff(c_314, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, B_90) | ~r2_hidden(C_91, A_89))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.41/11.57  tff(c_1084, plain, (![C_177, B_178, A_179]: (~r2_hidden(C_177, B_178) | ~r2_hidden(C_177, k1_tarski(A_179)) | r2_hidden(A_179, B_178))), inference(resolution, [status(thm)], [c_34, c_314])).
% 20.41/11.57  tff(c_4293, plain, (![A_359, B_360, A_361]: (~r2_hidden('#skF_2'(A_359, B_360), k1_tarski(A_361)) | r2_hidden(A_361, A_359) | r1_xboole_0(A_359, B_360))), inference(resolution, [status(thm)], [c_14, c_1084])).
% 20.41/11.57  tff(c_4324, plain, (![A_362, A_363]: (r2_hidden(A_362, A_363) | r1_xboole_0(A_363, k1_tarski(A_362)))), inference(resolution, [status(thm)], [c_12, c_4293])).
% 20.41/11.57  tff(c_10, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, B_9) | ~r2_hidden(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.41/11.57  tff(c_33399, plain, (![C_1540, A_1541, A_1542]: (~r2_hidden(C_1540, k1_tarski(A_1541)) | ~r2_hidden(C_1540, A_1542) | r2_hidden(A_1541, A_1542))), inference(resolution, [status(thm)], [c_4324, c_10])).
% 20.41/11.57  tff(c_33663, plain, (![A_1542]: (~r2_hidden(k1_mcart_1('#skF_3'), A_1542) | r2_hidden('#skF_4', A_1542))), inference(resolution, [status(thm)], [c_398, c_33399])).
% 20.41/11.57  tff(c_42095, plain, (r2_hidden('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42090, c_33663])).
% 20.41/11.57  tff(c_42109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2814, c_42095])).
% 20.41/11.57  tff(c_42110, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 20.41/11.57  tff(c_42405, plain, (![A_1815, C_1816, B_1817]: (r2_hidden(k2_mcart_1(A_1815), C_1816) | ~r2_hidden(A_1815, k2_zfmisc_1(B_1817, C_1816)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 20.41/11.57  tff(c_42416, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_52, c_42405])).
% 20.41/11.57  tff(c_42423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42110, c_42416])).
% 20.41/11.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.41/11.57  
% 20.41/11.57  Inference rules
% 20.41/11.57  ----------------------
% 20.41/11.57  #Ref     : 0
% 20.41/11.57  #Sup     : 9242
% 20.41/11.57  #Fact    : 0
% 20.41/11.57  #Define  : 0
% 20.41/11.57  #Split   : 2
% 20.41/11.57  #Chain   : 0
% 20.41/11.57  #Close   : 0
% 20.41/11.57  
% 20.41/11.57  Ordering : KBO
% 20.41/11.57  
% 20.41/11.57  Simplification rules
% 20.41/11.57  ----------------------
% 20.41/11.57  #Subsume      : 1806
% 20.41/11.57  #Demod        : 883
% 20.41/11.57  #Tautology    : 941
% 20.41/11.57  #SimpNegUnit  : 42
% 20.41/11.57  #BackRed      : 0
% 20.41/11.57  
% 20.41/11.57  #Partial instantiations: 0
% 20.41/11.57  #Strategies tried      : 1
% 20.41/11.57  
% 20.41/11.57  Timing (in seconds)
% 20.41/11.57  ----------------------
% 20.41/11.57  Preprocessing        : 0.32
% 20.41/11.57  Parsing              : 0.17
% 20.41/11.57  CNF conversion       : 0.02
% 20.41/11.57  Main loop            : 10.49
% 20.41/11.57  Inferencing          : 1.81
% 20.41/11.57  Reduction            : 4.08
% 20.41/11.57  Demodulation         : 2.71
% 20.41/11.57  BG Simplification    : 0.14
% 20.41/11.57  Subsumption          : 3.83
% 20.41/11.57  Abstraction          : 0.18
% 20.41/11.57  MUC search           : 0.00
% 20.41/11.57  Cooper               : 0.00
% 20.41/11.57  Total                : 10.84
% 20.41/11.57  Index Insertion      : 0.00
% 20.41/11.57  Index Deletion       : 0.00
% 20.41/11.57  Index Matching       : 0.00
% 20.41/11.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
