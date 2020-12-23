%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:48 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 356 expanded)
%              Number of leaves         :   18 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :  147 ( 789 expanded)
%              Number of equality atoms :   81 ( 405 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(c_4512,plain,(
    ! [A_2207,B_2208,C_2209] :
      ( r2_hidden('#skF_1'(A_2207,B_2208,C_2209),A_2207)
      | r2_hidden('#skF_2'(A_2207,B_2208,C_2209),C_2209)
      | k4_xboole_0(A_2207,B_2208) = C_2209 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4599,plain,(
    ! [A_2225,C_2226] :
      ( r2_hidden('#skF_2'(A_2225,A_2225,C_2226),C_2226)
      | k4_xboole_0(A_2225,A_2225) = C_2226 ) ),
    inference(resolution,[status(thm)],[c_4512,c_16])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k1_tarski(A_13),B_14) = k1_xboole_0
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [D_23,B_24,A_25] :
      ( ~ r2_hidden(D_23,B_24)
      | ~ r2_hidden(D_23,k4_xboole_0(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [D_31,B_32,A_33] :
      ( ~ r2_hidden(D_31,B_32)
      | ~ r2_hidden(D_31,k1_xboole_0)
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_77])).

tff(c_102,plain,(
    ! [C_34,A_35] :
      ( ~ r2_hidden(C_34,k1_xboole_0)
      | ~ r2_hidden(A_35,k1_tarski(C_34)) ) ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_106,plain,(
    ! [C_11] : ~ r2_hidden(C_11,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_4639,plain,(
    ! [A_2225] : k4_xboole_0(A_2225,A_2225) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4599,c_106])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    ! [A_36] :
      ( '#skF_3'(A_36,'#skF_5') = A_36
      | '#skF_4'(A_36,'#skF_5') != A_36
      | k1_tarski(A_36) = '#skF_5' ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_218,plain,
    ( k4_xboole_0('#skF_5','#skF_5') = k1_xboole_0
    | '#skF_3'('#skF_6','#skF_5') = '#skF_6'
    | '#skF_4'('#skF_6','#skF_5') != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_42])).

tff(c_465,plain,(
    '#skF_4'('#skF_6','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_507,plain,(
    ! [A_547,B_548] :
      ( '#skF_3'(A_547,B_548) = A_547
      | r2_hidden('#skF_4'(A_547,B_548),B_548)
      | k1_tarski(A_547) = B_548 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_326,plain,(
    ! [D_366,A_367,B_368] :
      ( r2_hidden(D_366,k4_xboole_0(A_367,B_368))
      | r2_hidden(D_366,B_368)
      | ~ r2_hidden(D_366,A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_339,plain,(
    ! [D_366] :
      ( r2_hidden(D_366,k1_xboole_0)
      | r2_hidden(D_366,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_366,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_326])).

tff(c_344,plain,(
    ! [D_384] :
      ( r2_hidden(D_384,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_384,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_339])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_376,plain,(
    ! [D_384] :
      ( D_384 = '#skF_6'
      | ~ r2_hidden(D_384,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_344,c_20])).

tff(c_695,plain,(
    ! [A_613] :
      ( '#skF_4'(A_613,'#skF_5') = '#skF_6'
      | '#skF_3'(A_613,'#skF_5') = A_613
      | k1_tarski(A_613) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_507,c_376])).

tff(c_724,plain,
    ( '#skF_4'('#skF_6','#skF_5') = '#skF_6'
    | '#skF_3'('#skF_6','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_38])).

tff(c_763,plain,(
    '#skF_3'('#skF_6','#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_724])).

tff(c_28,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r2_hidden('#skF_4'(A_7,B_8),B_8)
      | k1_tarski(A_7) = B_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_771,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5')
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_28])).

tff(c_791,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_771])).

tff(c_797,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_803,plain,(
    ! [A_659,B_660,C_661] :
      ( r2_hidden('#skF_1'(A_659,B_660,C_661),A_659)
      | r2_hidden('#skF_2'(A_659,B_660,C_661),C_661)
      | k4_xboole_0(A_659,B_660) = C_661 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_858,plain,(
    ! [B_677,C_678] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_677,C_678),C_678)
      | k4_xboole_0(k1_xboole_0,B_677) = C_678 ) ),
    inference(resolution,[status(thm)],[c_803,c_106])).

tff(c_885,plain,(
    ! [B_677] : k4_xboole_0(k1_xboole_0,B_677) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_858,c_106])).

tff(c_850,plain,(
    ! [B_660,C_661] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_660,C_661),C_661)
      | k4_xboole_0(k1_xboole_0,B_660) = C_661 ) ),
    inference(resolution,[status(thm)],[c_803,c_106])).

tff(c_909,plain,(
    ! [B_710,C_711] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_710,C_711),C_711)
      | k1_xboole_0 = C_711 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_850])).

tff(c_916,plain,(
    ! [B_710] :
      ( '#skF_2'(k1_xboole_0,B_710,'#skF_5') = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_909,c_376])).

tff(c_943,plain,(
    ! [B_727] : '#skF_2'(k1_xboole_0,B_727,'#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_916])).

tff(c_889,plain,(
    ! [B_660,C_661] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_660,C_661),C_661)
      | k1_xboole_0 = C_661 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_850])).

tff(c_948,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_889])).

tff(c_955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_797,c_948])).

tff(c_956,plain,(
    r2_hidden('#skF_4'('#skF_6','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_968,plain,(
    '#skF_4'('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_956,c_376])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_968])).

tff(c_974,plain,(
    '#skF_4'('#skF_6','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_995,plain,(
    ! [A_803,B_804] :
      ( '#skF_3'(A_803,B_804) = A_803
      | r2_hidden('#skF_4'(A_803,B_804),B_804)
      | k1_tarski(A_803) = B_804 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1021,plain,
    ( '#skF_3'('#skF_6','#skF_5') = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_995])).

tff(c_1039,plain,
    ( '#skF_3'('#skF_6','#skF_5') = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1021])).

tff(c_1040,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1039])).

tff(c_109,plain,(
    ! [A_36,B_37] :
      ( '#skF_3'(A_36,B_37) = A_36
      | '#skF_4'(A_36,B_37) != A_36
      | k1_tarski(A_36) = B_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_267,plain,(
    ! [B_37] :
      ( B_37 != '#skF_5'
      | '#skF_3'('#skF_6',B_37) = '#skF_6'
      | '#skF_4'('#skF_6',B_37) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_38])).

tff(c_389,plain,(
    ! [A_434,B_435] :
      ( ~ r2_hidden('#skF_3'(A_434,B_435),B_435)
      | '#skF_4'(A_434,B_435) != A_434
      | k1_tarski(A_434) = B_435 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1915,plain,(
    ! [B_1153] :
      ( ~ r2_hidden('#skF_6',B_1153)
      | '#skF_4'('#skF_6',B_1153) != '#skF_6'
      | k1_tarski('#skF_6') = B_1153
      | B_1153 != '#skF_5'
      | '#skF_4'('#skF_6',B_1153) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_389])).

tff(c_1933,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | '#skF_4'('#skF_6','#skF_5') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_1040,c_1915])).

tff(c_1974,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_1933])).

tff(c_1976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1974])).

tff(c_1978,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1039])).

tff(c_973,plain,
    ( '#skF_3'('#skF_6','#skF_5') = '#skF_6'
    | k4_xboole_0('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_979,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_3027,plain,(
    ! [A_1598,B_1599,C_1600] :
      ( r2_hidden('#skF_1'(A_1598,B_1599,C_1600),A_1598)
      | r2_hidden('#skF_2'(A_1598,B_1599,C_1600),C_1600)
      | k4_xboole_0(A_1598,B_1599) = C_1600 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3166,plain,(
    ! [A_1632,B_1633] :
      ( r2_hidden('#skF_2'(A_1632,B_1633,A_1632),A_1632)
      | k4_xboole_0(A_1632,B_1633) = A_1632 ) ),
    inference(resolution,[status(thm)],[c_3027,c_14])).

tff(c_3295,plain,(
    ! [B_1681] :
      ( '#skF_2'('#skF_5',B_1681,'#skF_5') = '#skF_6'
      | k4_xboole_0('#skF_5',B_1681) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3166,c_376])).

tff(c_3304,plain,
    ( k1_xboole_0 = '#skF_5'
    | '#skF_2'('#skF_5','#skF_5','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3295,c_979])).

tff(c_3328,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3304])).

tff(c_3098,plain,(
    ! [A_1598,B_1599] :
      ( r2_hidden('#skF_2'(A_1598,B_1599,A_1598),A_1598)
      | k4_xboole_0(A_1598,B_1599) = A_1598 ) ),
    inference(resolution,[status(thm)],[c_3027,c_14])).

tff(c_3336,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3328,c_3098])).

tff(c_3340,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_3336])).

tff(c_3342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1978,c_3340])).

tff(c_3344,plain,(
    k4_xboole_0('#skF_5','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_4646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4639,c_3344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.90  
% 4.47/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.90  %$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.47/1.90  
% 4.47/1.90  %Foreground sorts:
% 4.47/1.90  
% 4.47/1.90  
% 4.47/1.90  %Background operators:
% 4.47/1.90  
% 4.47/1.90  
% 4.47/1.90  %Foreground operators:
% 4.47/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.47/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.47/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.47/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.47/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.47/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.47/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.47/1.90  
% 4.80/1.92  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.80/1.92  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.80/1.92  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 4.80/1.92  tff(f_58, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.80/1.92  tff(c_4512, plain, (![A_2207, B_2208, C_2209]: (r2_hidden('#skF_1'(A_2207, B_2208, C_2209), A_2207) | r2_hidden('#skF_2'(A_2207, B_2208, C_2209), C_2209) | k4_xboole_0(A_2207, B_2208)=C_2209)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_4599, plain, (![A_2225, C_2226]: (r2_hidden('#skF_2'(A_2225, A_2225, C_2226), C_2226) | k4_xboole_0(A_2225, A_2225)=C_2226)), inference(resolution, [status(thm)], [c_4512, c_16])).
% 4.80/1.92  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_36, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), B_14)=k1_xboole_0 | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.80/1.92  tff(c_77, plain, (![D_23, B_24, A_25]: (~r2_hidden(D_23, B_24) | ~r2_hidden(D_23, k4_xboole_0(A_25, B_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_98, plain, (![D_31, B_32, A_33]: (~r2_hidden(D_31, B_32) | ~r2_hidden(D_31, k1_xboole_0) | ~r2_hidden(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_36, c_77])).
% 4.80/1.92  tff(c_102, plain, (![C_34, A_35]: (~r2_hidden(C_34, k1_xboole_0) | ~r2_hidden(A_35, k1_tarski(C_34)))), inference(resolution, [status(thm)], [c_22, c_98])).
% 4.80/1.92  tff(c_106, plain, (![C_11]: (~r2_hidden(C_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_102])).
% 4.80/1.92  tff(c_4639, plain, (![A_2225]: (k4_xboole_0(A_2225, A_2225)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4599, c_106])).
% 4.80/1.92  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.80/1.92  tff(c_38, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.80/1.92  tff(c_215, plain, (![A_36]: ('#skF_3'(A_36, '#skF_5')=A_36 | '#skF_4'(A_36, '#skF_5')!=A_36 | k1_tarski(A_36)='#skF_5')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_42, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.80/1.92  tff(c_218, plain, (k4_xboole_0('#skF_5', '#skF_5')=k1_xboole_0 | '#skF_3'('#skF_6', '#skF_5')='#skF_6' | '#skF_4'('#skF_6', '#skF_5')!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_215, c_42])).
% 4.80/1.92  tff(c_465, plain, ('#skF_4'('#skF_6', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_218])).
% 4.80/1.92  tff(c_507, plain, (![A_547, B_548]: ('#skF_3'(A_547, B_548)=A_547 | r2_hidden('#skF_4'(A_547, B_548), B_548) | k1_tarski(A_547)=B_548)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_326, plain, (![D_366, A_367, B_368]: (r2_hidden(D_366, k4_xboole_0(A_367, B_368)) | r2_hidden(D_366, B_368) | ~r2_hidden(D_366, A_367))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_339, plain, (![D_366]: (r2_hidden(D_366, k1_xboole_0) | r2_hidden(D_366, k1_tarski('#skF_6')) | ~r2_hidden(D_366, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_326])).
% 4.80/1.92  tff(c_344, plain, (![D_384]: (r2_hidden(D_384, k1_tarski('#skF_6')) | ~r2_hidden(D_384, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_106, c_339])).
% 4.80/1.92  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_376, plain, (![D_384]: (D_384='#skF_6' | ~r2_hidden(D_384, '#skF_5'))), inference(resolution, [status(thm)], [c_344, c_20])).
% 4.80/1.92  tff(c_695, plain, (![A_613]: ('#skF_4'(A_613, '#skF_5')='#skF_6' | '#skF_3'(A_613, '#skF_5')=A_613 | k1_tarski(A_613)='#skF_5')), inference(resolution, [status(thm)], [c_507, c_376])).
% 4.80/1.92  tff(c_724, plain, ('#skF_4'('#skF_6', '#skF_5')='#skF_6' | '#skF_3'('#skF_6', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_695, c_38])).
% 4.80/1.92  tff(c_763, plain, ('#skF_3'('#skF_6', '#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_465, c_724])).
% 4.80/1.92  tff(c_28, plain, (![A_7, B_8]: (~r2_hidden('#skF_3'(A_7, B_8), B_8) | r2_hidden('#skF_4'(A_7, B_8), B_8) | k1_tarski(A_7)=B_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_771, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5') | k1_tarski('#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_763, c_28])).
% 4.80/1.92  tff(c_791, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_771])).
% 4.80/1.92  tff(c_797, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_791])).
% 4.80/1.92  tff(c_803, plain, (![A_659, B_660, C_661]: (r2_hidden('#skF_1'(A_659, B_660, C_661), A_659) | r2_hidden('#skF_2'(A_659, B_660, C_661), C_661) | k4_xboole_0(A_659, B_660)=C_661)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_858, plain, (![B_677, C_678]: (r2_hidden('#skF_2'(k1_xboole_0, B_677, C_678), C_678) | k4_xboole_0(k1_xboole_0, B_677)=C_678)), inference(resolution, [status(thm)], [c_803, c_106])).
% 4.80/1.92  tff(c_885, plain, (![B_677]: (k4_xboole_0(k1_xboole_0, B_677)=k1_xboole_0)), inference(resolution, [status(thm)], [c_858, c_106])).
% 4.80/1.92  tff(c_850, plain, (![B_660, C_661]: (r2_hidden('#skF_2'(k1_xboole_0, B_660, C_661), C_661) | k4_xboole_0(k1_xboole_0, B_660)=C_661)), inference(resolution, [status(thm)], [c_803, c_106])).
% 4.80/1.92  tff(c_909, plain, (![B_710, C_711]: (r2_hidden('#skF_2'(k1_xboole_0, B_710, C_711), C_711) | k1_xboole_0=C_711)), inference(demodulation, [status(thm), theory('equality')], [c_885, c_850])).
% 4.80/1.92  tff(c_916, plain, (![B_710]: ('#skF_2'(k1_xboole_0, B_710, '#skF_5')='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_909, c_376])).
% 4.80/1.92  tff(c_943, plain, (![B_727]: ('#skF_2'(k1_xboole_0, B_727, '#skF_5')='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_916])).
% 4.80/1.92  tff(c_889, plain, (![B_660, C_661]: (r2_hidden('#skF_2'(k1_xboole_0, B_660, C_661), C_661) | k1_xboole_0=C_661)), inference(demodulation, [status(thm), theory('equality')], [c_885, c_850])).
% 4.80/1.92  tff(c_948, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_943, c_889])).
% 4.80/1.92  tff(c_955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_797, c_948])).
% 4.80/1.92  tff(c_956, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_791])).
% 4.80/1.92  tff(c_968, plain, ('#skF_4'('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_956, c_376])).
% 4.80/1.92  tff(c_972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_465, c_968])).
% 4.80/1.92  tff(c_974, plain, ('#skF_4'('#skF_6', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_218])).
% 4.80/1.92  tff(c_995, plain, (![A_803, B_804]: ('#skF_3'(A_803, B_804)=A_803 | r2_hidden('#skF_4'(A_803, B_804), B_804) | k1_tarski(A_803)=B_804)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_1021, plain, ('#skF_3'('#skF_6', '#skF_5')='#skF_6' | r2_hidden('#skF_6', '#skF_5') | k1_tarski('#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_974, c_995])).
% 4.80/1.92  tff(c_1039, plain, ('#skF_3'('#skF_6', '#skF_5')='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_1021])).
% 4.80/1.92  tff(c_1040, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1039])).
% 4.80/1.92  tff(c_109, plain, (![A_36, B_37]: ('#skF_3'(A_36, B_37)=A_36 | '#skF_4'(A_36, B_37)!=A_36 | k1_tarski(A_36)=B_37)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_267, plain, (![B_37]: (B_37!='#skF_5' | '#skF_3'('#skF_6', B_37)='#skF_6' | '#skF_4'('#skF_6', B_37)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_109, c_38])).
% 4.80/1.92  tff(c_389, plain, (![A_434, B_435]: (~r2_hidden('#skF_3'(A_434, B_435), B_435) | '#skF_4'(A_434, B_435)!=A_434 | k1_tarski(A_434)=B_435)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.92  tff(c_1915, plain, (![B_1153]: (~r2_hidden('#skF_6', B_1153) | '#skF_4'('#skF_6', B_1153)!='#skF_6' | k1_tarski('#skF_6')=B_1153 | B_1153!='#skF_5' | '#skF_4'('#skF_6', B_1153)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_267, c_389])).
% 4.80/1.92  tff(c_1933, plain, (k1_tarski('#skF_6')='#skF_5' | '#skF_4'('#skF_6', '#skF_5')!='#skF_6'), inference(resolution, [status(thm)], [c_1040, c_1915])).
% 4.80/1.92  tff(c_1974, plain, (k1_tarski('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_974, c_1933])).
% 4.80/1.92  tff(c_1976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1974])).
% 4.80/1.92  tff(c_1978, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_1039])).
% 4.80/1.92  tff(c_973, plain, ('#skF_3'('#skF_6', '#skF_5')='#skF_6' | k4_xboole_0('#skF_5', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_218])).
% 4.80/1.92  tff(c_979, plain, (k4_xboole_0('#skF_5', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_973])).
% 4.80/1.92  tff(c_3027, plain, (![A_1598, B_1599, C_1600]: (r2_hidden('#skF_1'(A_1598, B_1599, C_1600), A_1598) | r2_hidden('#skF_2'(A_1598, B_1599, C_1600), C_1600) | k4_xboole_0(A_1598, B_1599)=C_1600)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.92  tff(c_3166, plain, (![A_1632, B_1633]: (r2_hidden('#skF_2'(A_1632, B_1633, A_1632), A_1632) | k4_xboole_0(A_1632, B_1633)=A_1632)), inference(resolution, [status(thm)], [c_3027, c_14])).
% 4.80/1.92  tff(c_3295, plain, (![B_1681]: ('#skF_2'('#skF_5', B_1681, '#skF_5')='#skF_6' | k4_xboole_0('#skF_5', B_1681)='#skF_5')), inference(resolution, [status(thm)], [c_3166, c_376])).
% 4.80/1.92  tff(c_3304, plain, (k1_xboole_0='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3295, c_979])).
% 4.80/1.92  tff(c_3328, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_3304])).
% 4.80/1.92  tff(c_3098, plain, (![A_1598, B_1599]: (r2_hidden('#skF_2'(A_1598, B_1599, A_1598), A_1598) | k4_xboole_0(A_1598, B_1599)=A_1598)), inference(resolution, [status(thm)], [c_3027, c_14])).
% 4.80/1.92  tff(c_3336, plain, (r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3328, c_3098])).
% 4.80/1.92  tff(c_3340, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_3336])).
% 4.80/1.92  tff(c_3342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1978, c_3340])).
% 4.80/1.92  tff(c_3344, plain, (k4_xboole_0('#skF_5', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_973])).
% 4.80/1.92  tff(c_4646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4639, c_3344])).
% 4.80/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.92  
% 4.80/1.92  Inference rules
% 4.80/1.92  ----------------------
% 4.80/1.92  #Ref     : 0
% 4.80/1.92  #Sup     : 853
% 4.80/1.92  #Fact    : 0
% 4.80/1.92  #Define  : 0
% 4.80/1.92  #Split   : 9
% 4.80/1.92  #Chain   : 0
% 4.80/1.92  #Close   : 0
% 4.80/1.92  
% 4.80/1.92  Ordering : KBO
% 4.80/1.92  
% 4.80/1.92  Simplification rules
% 4.80/1.92  ----------------------
% 4.80/1.92  #Subsume      : 184
% 4.80/1.92  #Demod        : 193
% 4.80/1.92  #Tautology    : 286
% 4.80/1.92  #SimpNegUnit  : 91
% 4.80/1.92  #BackRed      : 4
% 4.80/1.92  
% 4.80/1.92  #Partial instantiations: 1340
% 4.80/1.92  #Strategies tried      : 1
% 4.80/1.92  
% 4.80/1.92  Timing (in seconds)
% 4.80/1.92  ----------------------
% 4.80/1.92  Preprocessing        : 0.29
% 4.80/1.92  Parsing              : 0.14
% 4.80/1.92  CNF conversion       : 0.02
% 4.80/1.92  Main loop            : 0.85
% 4.80/1.92  Inferencing          : 0.36
% 4.80/1.92  Reduction            : 0.22
% 4.80/1.92  Demodulation         : 0.14
% 4.80/1.92  BG Simplification    : 0.04
% 4.80/1.92  Subsumption          : 0.17
% 4.80/1.92  Abstraction          : 0.04
% 4.80/1.92  MUC search           : 0.00
% 4.80/1.92  Cooper               : 0.00
% 4.80/1.92  Total                : 1.18
% 4.80/1.92  Index Insertion      : 0.00
% 4.80/1.92  Index Deletion       : 0.00
% 4.80/1.92  Index Matching       : 0.00
% 4.80/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
