%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 145 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 334 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
            | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
          & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
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

tff(c_40,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3117,plain,(
    ! [A_356,B_357,C_358] :
      ( r2_hidden('#skF_2'(A_356,B_357,C_358),B_357)
      | r2_hidden('#skF_3'(A_356,B_357,C_358),C_358)
      | k3_xboole_0(A_356,B_357) = C_358 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3150,plain,(
    ! [A_356,B_357] :
      ( r2_hidden('#skF_3'(A_356,B_357,B_357),B_357)
      | k3_xboole_0(A_356,B_357) = B_357 ) ),
    inference(resolution,[status(thm)],[c_3117,c_20])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_385,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r2_hidden('#skF_2'(A_95,B_96,C_97),C_97)
      | r2_hidden('#skF_3'(A_95,B_96,C_97),C_97)
      | k3_xboole_0(A_95,B_96) = C_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_399,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,B_7),B_7)
      | k3_xboole_0(A_6,B_7) = B_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_385])).

tff(c_42,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_5','#skF_7'))
    | r1_tarski(k2_zfmisc_1('#skF_6','#skF_5'),k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,(
    r1_tarski(k2_zfmisc_1('#skF_6','#skF_5'),k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_197,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( r2_hidden(k4_tarski(A_69,B_70),k2_zfmisc_1(C_71,D_72))
      | ~ r2_hidden(B_70,D_72)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2147,plain,(
    ! [B_270,A_271,C_274,D_272,B_273] :
      ( r2_hidden(k4_tarski(A_271,B_270),B_273)
      | ~ r1_tarski(k2_zfmisc_1(C_274,D_272),B_273)
      | ~ r2_hidden(B_270,D_272)
      | ~ r2_hidden(A_271,C_274) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_2347,plain,(
    ! [A_287,B_288] :
      ( r2_hidden(k4_tarski(A_287,B_288),k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(B_288,'#skF_5')
      | ~ r2_hidden(A_287,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_87,c_2147])).

tff(c_38,plain,(
    ! [A_18,C_20,B_19,D_21] :
      ( r2_hidden(A_18,C_20)
      | ~ r2_hidden(k4_tarski(A_18,B_19),k2_zfmisc_1(C_20,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2363,plain,(
    ! [A_287,B_288] :
      ( r2_hidden(A_287,'#skF_7')
      | ~ r2_hidden(B_288,'#skF_5')
      | ~ r2_hidden(A_287,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2347,c_38])).

tff(c_2366,plain,(
    ! [B_289] : ~ r2_hidden(B_289,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2363])).

tff(c_2575,plain,(
    ! [A_295] : k3_xboole_0(A_295,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_399,c_2366])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_398,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k3_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_385])).

tff(c_438,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_3'(A_101,B_102,A_101),A_101)
      | k3_xboole_0(A_101,B_102) = A_101 ) ),
    inference(resolution,[status(thm)],[c_24,c_385])).

tff(c_32,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,B_42)
      | ~ r2_hidden(C_43,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [C_43,A_17] :
      ( ~ r2_hidden(C_43,k1_xboole_0)
      | ~ r2_hidden(C_43,A_17) ) ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_486,plain,(
    ! [B_105,A_106] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_105,k1_xboole_0),A_106)
      | k3_xboole_0(k1_xboole_0,B_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_438,c_102])).

tff(c_504,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_398,c_486])).

tff(c_2704,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2575,c_504])).

tff(c_2777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2704])).

tff(c_2779,plain,(
    ! [A_296] :
      ( r2_hidden(A_296,'#skF_7')
      | ~ r2_hidden(A_296,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_2363])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2821,plain,(
    ! [A_297] :
      ( r1_tarski(A_297,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_297,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2779,c_4])).

tff(c_2837,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_2821])).

tff(c_2844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_2837])).

tff(c_2845,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2956,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( r2_hidden(k4_tarski(A_330,B_331),k2_zfmisc_1(C_332,D_333))
      | ~ r2_hidden(B_331,D_333)
      | ~ r2_hidden(A_330,C_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4912,plain,(
    ! [A_532,B_533,B_531,D_534,C_530] :
      ( r2_hidden(k4_tarski(A_532,B_533),B_531)
      | ~ r1_tarski(k2_zfmisc_1(C_530,D_534),B_531)
      | ~ r2_hidden(B_533,D_534)
      | ~ r2_hidden(A_532,C_530) ) ),
    inference(resolution,[status(thm)],[c_2956,c_2])).

tff(c_5056,plain,(
    ! [A_543,B_544] :
      ( r2_hidden(k4_tarski(A_543,B_544),k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(B_544,'#skF_6')
      | ~ r2_hidden(A_543,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2845,c_4912])).

tff(c_36,plain,(
    ! [B_19,D_21,A_18,C_20] :
      ( r2_hidden(B_19,D_21)
      | ~ r2_hidden(k4_tarski(A_18,B_19),k2_zfmisc_1(C_20,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5072,plain,(
    ! [B_544,A_543] :
      ( r2_hidden(B_544,'#skF_7')
      | ~ r2_hidden(B_544,'#skF_6')
      | ~ r2_hidden(A_543,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5056,c_36])).

tff(c_5075,plain,(
    ! [A_545] : ~ r2_hidden(A_545,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5072])).

tff(c_5226,plain,(
    ! [A_549] : k3_xboole_0(A_549,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3150,c_5075])).

tff(c_3102,plain,(
    ! [A_351,B_352,C_353] :
      ( ~ r2_hidden('#skF_2'(A_351,B_352,C_353),C_353)
      | r2_hidden('#skF_3'(A_351,B_352,C_353),C_353)
      | k3_xboole_0(A_351,B_352) = C_353 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3111,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k3_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_3102])).

tff(c_3197,plain,(
    ! [A_362,B_363] :
      ( r2_hidden('#skF_3'(A_362,B_363,A_362),A_362)
      | k3_xboole_0(A_362,B_363) = A_362 ) ),
    inference(resolution,[status(thm)],[c_24,c_3102])).

tff(c_2858,plain,(
    ! [A_302,B_303,C_304] :
      ( ~ r1_xboole_0(A_302,B_303)
      | ~ r2_hidden(C_304,B_303)
      | ~ r2_hidden(C_304,A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2861,plain,(
    ! [C_304,A_17] :
      ( ~ r2_hidden(C_304,k1_xboole_0)
      | ~ r2_hidden(C_304,A_17) ) ),
    inference(resolution,[status(thm)],[c_32,c_2858])).

tff(c_3245,plain,(
    ! [B_366,A_367] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_366,k1_xboole_0),A_367)
      | k3_xboole_0(k1_xboole_0,B_366) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3197,c_2861])).

tff(c_3263,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3111,c_3245])).

tff(c_5351,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5226,c_3263])).

tff(c_5424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5351])).

tff(c_5475,plain,(
    ! [B_552] :
      ( r2_hidden(B_552,'#skF_7')
      | ~ r2_hidden(B_552,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_5072])).

tff(c_5517,plain,(
    ! [A_553] :
      ( r1_tarski(A_553,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_553,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5475,c_4])).

tff(c_5533,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_5517])).

tff(c_5540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_5533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:27:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.23/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.96  
% 5.23/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.23/1.97  
% 5.23/1.97  %Foreground sorts:
% 5.23/1.97  
% 5.23/1.97  
% 5.23/1.97  %Background operators:
% 5.23/1.97  
% 5.23/1.97  
% 5.23/1.97  %Foreground operators:
% 5.23/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/1.97  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.23/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.23/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.23/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.23/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.23/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.23/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/1.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.23/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.23/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.23/1.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.23/1.97  
% 5.52/1.98  tff(f_79, negated_conjecture, ~(![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 5.52/1.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.52/1.98  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.52/1.98  tff(f_67, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.52/1.98  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.52/1.98  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.52/1.98  tff(c_40, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.52/1.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/1.98  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.52/1.98  tff(c_3117, plain, (![A_356, B_357, C_358]: (r2_hidden('#skF_2'(A_356, B_357, C_358), B_357) | r2_hidden('#skF_3'(A_356, B_357, C_358), C_358) | k3_xboole_0(A_356, B_357)=C_358)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/1.98  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/1.98  tff(c_3150, plain, (![A_356, B_357]: (r2_hidden('#skF_3'(A_356, B_357, B_357), B_357) | k3_xboole_0(A_356, B_357)=B_357)), inference(resolution, [status(thm)], [c_3117, c_20])).
% 5.52/1.98  tff(c_22, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/1.98  tff(c_385, plain, (![A_95, B_96, C_97]: (~r2_hidden('#skF_2'(A_95, B_96, C_97), C_97) | r2_hidden('#skF_3'(A_95, B_96, C_97), C_97) | k3_xboole_0(A_95, B_96)=C_97)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/1.98  tff(c_399, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, B_7), B_7) | k3_xboole_0(A_6, B_7)=B_7)), inference(resolution, [status(thm)], [c_22, c_385])).
% 5.52/1.98  tff(c_42, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_7')) | r1_tarski(k2_zfmisc_1('#skF_6', '#skF_5'), k2_zfmisc_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.52/1.98  tff(c_87, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_5'), k2_zfmisc_1('#skF_7', '#skF_5'))), inference(splitLeft, [status(thm)], [c_42])).
% 5.52/1.98  tff(c_197, plain, (![A_69, B_70, C_71, D_72]: (r2_hidden(k4_tarski(A_69, B_70), k2_zfmisc_1(C_71, D_72)) | ~r2_hidden(B_70, D_72) | ~r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.52/1.98  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/1.98  tff(c_2147, plain, (![B_270, A_271, C_274, D_272, B_273]: (r2_hidden(k4_tarski(A_271, B_270), B_273) | ~r1_tarski(k2_zfmisc_1(C_274, D_272), B_273) | ~r2_hidden(B_270, D_272) | ~r2_hidden(A_271, C_274))), inference(resolution, [status(thm)], [c_197, c_2])).
% 5.52/1.98  tff(c_2347, plain, (![A_287, B_288]: (r2_hidden(k4_tarski(A_287, B_288), k2_zfmisc_1('#skF_7', '#skF_5')) | ~r2_hidden(B_288, '#skF_5') | ~r2_hidden(A_287, '#skF_6'))), inference(resolution, [status(thm)], [c_87, c_2147])).
% 5.52/1.98  tff(c_38, plain, (![A_18, C_20, B_19, D_21]: (r2_hidden(A_18, C_20) | ~r2_hidden(k4_tarski(A_18, B_19), k2_zfmisc_1(C_20, D_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.52/1.98  tff(c_2363, plain, (![A_287, B_288]: (r2_hidden(A_287, '#skF_7') | ~r2_hidden(B_288, '#skF_5') | ~r2_hidden(A_287, '#skF_6'))), inference(resolution, [status(thm)], [c_2347, c_38])).
% 5.52/1.98  tff(c_2366, plain, (![B_289]: (~r2_hidden(B_289, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2363])).
% 5.52/1.98  tff(c_2575, plain, (![A_295]: (k3_xboole_0(A_295, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_399, c_2366])).
% 5.52/1.98  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/1.98  tff(c_398, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k3_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_385])).
% 5.52/1.98  tff(c_438, plain, (![A_101, B_102]: (r2_hidden('#skF_3'(A_101, B_102, A_101), A_101) | k3_xboole_0(A_101, B_102)=A_101)), inference(resolution, [status(thm)], [c_24, c_385])).
% 5.52/1.98  tff(c_32, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.52/1.98  tff(c_99, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, B_42) | ~r2_hidden(C_43, A_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/1.98  tff(c_102, plain, (![C_43, A_17]: (~r2_hidden(C_43, k1_xboole_0) | ~r2_hidden(C_43, A_17))), inference(resolution, [status(thm)], [c_32, c_99])).
% 5.52/1.98  tff(c_486, plain, (![B_105, A_106]: (~r2_hidden('#skF_3'(k1_xboole_0, B_105, k1_xboole_0), A_106) | k3_xboole_0(k1_xboole_0, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_438, c_102])).
% 5.52/1.98  tff(c_504, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_398, c_486])).
% 5.52/1.98  tff(c_2704, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2575, c_504])).
% 5.52/1.98  tff(c_2777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2704])).
% 5.52/1.98  tff(c_2779, plain, (![A_296]: (r2_hidden(A_296, '#skF_7') | ~r2_hidden(A_296, '#skF_6'))), inference(splitRight, [status(thm)], [c_2363])).
% 5.52/1.98  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/1.98  tff(c_2821, plain, (![A_297]: (r1_tarski(A_297, '#skF_7') | ~r2_hidden('#skF_1'(A_297, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_2779, c_4])).
% 5.52/1.98  tff(c_2837, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_2821])).
% 5.52/1.98  tff(c_2844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_2837])).
% 5.52/1.98  tff(c_2845, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_42])).
% 5.52/1.98  tff(c_2956, plain, (![A_330, B_331, C_332, D_333]: (r2_hidden(k4_tarski(A_330, B_331), k2_zfmisc_1(C_332, D_333)) | ~r2_hidden(B_331, D_333) | ~r2_hidden(A_330, C_332))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.52/1.98  tff(c_4912, plain, (![A_532, B_533, B_531, D_534, C_530]: (r2_hidden(k4_tarski(A_532, B_533), B_531) | ~r1_tarski(k2_zfmisc_1(C_530, D_534), B_531) | ~r2_hidden(B_533, D_534) | ~r2_hidden(A_532, C_530))), inference(resolution, [status(thm)], [c_2956, c_2])).
% 5.52/1.98  tff(c_5056, plain, (![A_543, B_544]: (r2_hidden(k4_tarski(A_543, B_544), k2_zfmisc_1('#skF_5', '#skF_7')) | ~r2_hidden(B_544, '#skF_6') | ~r2_hidden(A_543, '#skF_5'))), inference(resolution, [status(thm)], [c_2845, c_4912])).
% 5.52/1.98  tff(c_36, plain, (![B_19, D_21, A_18, C_20]: (r2_hidden(B_19, D_21) | ~r2_hidden(k4_tarski(A_18, B_19), k2_zfmisc_1(C_20, D_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.52/1.98  tff(c_5072, plain, (![B_544, A_543]: (r2_hidden(B_544, '#skF_7') | ~r2_hidden(B_544, '#skF_6') | ~r2_hidden(A_543, '#skF_5'))), inference(resolution, [status(thm)], [c_5056, c_36])).
% 5.52/1.98  tff(c_5075, plain, (![A_545]: (~r2_hidden(A_545, '#skF_5'))), inference(splitLeft, [status(thm)], [c_5072])).
% 5.52/1.98  tff(c_5226, plain, (![A_549]: (k3_xboole_0(A_549, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_3150, c_5075])).
% 5.52/1.98  tff(c_3102, plain, (![A_351, B_352, C_353]: (~r2_hidden('#skF_2'(A_351, B_352, C_353), C_353) | r2_hidden('#skF_3'(A_351, B_352, C_353), C_353) | k3_xboole_0(A_351, B_352)=C_353)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.52/1.98  tff(c_3111, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k3_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_3102])).
% 5.52/1.98  tff(c_3197, plain, (![A_362, B_363]: (r2_hidden('#skF_3'(A_362, B_363, A_362), A_362) | k3_xboole_0(A_362, B_363)=A_362)), inference(resolution, [status(thm)], [c_24, c_3102])).
% 5.52/1.98  tff(c_2858, plain, (![A_302, B_303, C_304]: (~r1_xboole_0(A_302, B_303) | ~r2_hidden(C_304, B_303) | ~r2_hidden(C_304, A_302))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/1.98  tff(c_2861, plain, (![C_304, A_17]: (~r2_hidden(C_304, k1_xboole_0) | ~r2_hidden(C_304, A_17))), inference(resolution, [status(thm)], [c_32, c_2858])).
% 5.52/1.98  tff(c_3245, plain, (![B_366, A_367]: (~r2_hidden('#skF_3'(k1_xboole_0, B_366, k1_xboole_0), A_367) | k3_xboole_0(k1_xboole_0, B_366)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3197, c_2861])).
% 5.52/1.98  tff(c_3263, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3111, c_3245])).
% 5.52/1.98  tff(c_5351, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5226, c_3263])).
% 5.52/1.98  tff(c_5424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_5351])).
% 5.52/1.98  tff(c_5475, plain, (![B_552]: (r2_hidden(B_552, '#skF_7') | ~r2_hidden(B_552, '#skF_6'))), inference(splitRight, [status(thm)], [c_5072])).
% 5.52/1.98  tff(c_5517, plain, (![A_553]: (r1_tarski(A_553, '#skF_7') | ~r2_hidden('#skF_1'(A_553, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_5475, c_4])).
% 5.52/1.98  tff(c_5533, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_5517])).
% 5.52/1.98  tff(c_5540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_5533])).
% 5.52/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/1.98  
% 5.52/1.98  Inference rules
% 5.52/1.98  ----------------------
% 5.52/1.98  #Ref     : 0
% 5.52/1.98  #Sup     : 1326
% 5.52/1.98  #Fact    : 0
% 5.52/1.98  #Define  : 0
% 5.52/1.98  #Split   : 3
% 5.52/1.98  #Chain   : 0
% 5.52/1.98  #Close   : 0
% 5.52/1.98  
% 5.52/1.98  Ordering : KBO
% 5.52/1.98  
% 5.52/1.98  Simplification rules
% 5.52/1.98  ----------------------
% 5.52/1.98  #Subsume      : 414
% 5.52/1.98  #Demod        : 540
% 5.52/1.98  #Tautology    : 333
% 5.52/1.98  #SimpNegUnit  : 10
% 5.52/1.98  #BackRed      : 0
% 5.52/1.98  
% 5.52/1.98  #Partial instantiations: 0
% 5.52/1.98  #Strategies tried      : 1
% 5.52/1.98  
% 5.52/1.98  Timing (in seconds)
% 5.52/1.98  ----------------------
% 5.52/1.99  Preprocessing        : 0.28
% 5.52/1.99  Parsing              : 0.15
% 5.52/1.99  CNF conversion       : 0.02
% 5.52/1.99  Main loop            : 0.97
% 5.52/1.99  Inferencing          : 0.36
% 5.52/1.99  Reduction            : 0.26
% 5.52/1.99  Demodulation         : 0.18
% 5.52/1.99  BG Simplification    : 0.04
% 5.52/1.99  Subsumption          : 0.24
% 5.52/1.99  Abstraction          : 0.05
% 5.52/1.99  MUC search           : 0.00
% 5.52/1.99  Cooper               : 0.00
% 5.52/1.99  Total                : 1.29
% 5.52/1.99  Index Insertion      : 0.00
% 5.52/1.99  Index Deletion       : 0.00
% 5.52/1.99  Index Matching       : 0.00
% 5.52/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
