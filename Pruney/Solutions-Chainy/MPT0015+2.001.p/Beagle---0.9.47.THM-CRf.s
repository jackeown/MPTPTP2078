%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 19.35s
% Output     : CNFRefutation 19.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 298 expanded)
%              Number of leaves         :   15 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  133 ( 854 expanded)
%              Number of equality atoms :   24 ( 183 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,(
    ! [A_62,A_63,B_64] :
      ( r1_tarski(A_62,k2_xboole_0(A_63,B_64))
      | ~ r2_hidden('#skF_1'(A_62,k2_xboole_0(A_63,B_64)),B_64) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_240,plain,(
    ! [A_1,A_63] : r1_tarski(A_1,k2_xboole_0(A_63,A_1)) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2301,plain,(
    ! [A_240,C_241] :
      ( r2_hidden('#skF_3'(A_240,A_240,C_241),C_241)
      | k2_xboole_0(A_240,A_240) = C_241
      | r2_hidden('#skF_2'(A_240,A_240,C_241),A_240) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_24])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2382,plain,(
    ! [A_242] :
      ( r2_hidden('#skF_3'(A_242,A_242,A_242),A_242)
      | k2_xboole_0(A_242,A_242) = A_242 ) ),
    inference(resolution,[status(thm)],[c_2301,c_22])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1181,plain,(
    ! [B_170,C_171] :
      ( ~ r2_hidden('#skF_3'(B_170,B_170,C_171),B_170)
      | k2_xboole_0(B_170,B_170) = C_171
      | r2_hidden('#skF_2'(B_170,B_170,C_171),B_170) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_20])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1210,plain,(
    ! [B_170] :
      ( ~ r2_hidden('#skF_3'(B_170,B_170,B_170),B_170)
      | k2_xboole_0(B_170,B_170) = B_170 ) ),
    inference(resolution,[status(thm)],[c_1181,c_18])).

tff(c_2415,plain,(
    ! [A_242] : k2_xboole_0(A_242,A_242) = A_242 ),
    inference(resolution,[status(thm)],[c_2382,c_1210])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_1,B_2,B_24] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_24)
      | ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_40,A_41,B_42] :
      ( r1_tarski(A_40,k2_xboole_0(A_41,B_42))
      | ~ r2_hidden('#skF_1'(A_40,k2_xboole_0(A_41,B_42)),A_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

tff(c_116,plain,(
    ! [A_1,B_24,B_42] :
      ( ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,k2_xboole_0(B_24,B_42)) ) ),
    inference(resolution,[status(thm)],[c_58,c_99])).

tff(c_881,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_2'(A_142,B_143,C_144),B_143)
      | r2_hidden('#skF_2'(A_142,B_143,C_144),A_142)
      | r2_hidden('#skF_3'(A_142,B_143,C_144),C_144)
      | k2_xboole_0(A_142,B_143) = C_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4931,plain,(
    ! [A_355,B_356] :
      ( r2_hidden('#skF_2'(A_355,B_356,A_355),B_356)
      | r2_hidden('#skF_3'(A_355,B_356,A_355),A_355)
      | k2_xboole_0(A_355,B_356) = A_355 ) ),
    inference(resolution,[status(thm)],[c_881,c_22])).

tff(c_439,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden('#skF_2'(A_96,B_97,C_98),B_97)
      | r2_hidden('#skF_2'(A_96,B_97,C_98),A_96)
      | ~ r2_hidden('#skF_3'(A_96,B_97,C_98),A_96)
      | k2_xboole_0(A_96,B_97) = C_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_495,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_2'(A_96,B_97,A_96),B_97)
      | ~ r2_hidden('#skF_3'(A_96,B_97,A_96),A_96)
      | k2_xboole_0(A_96,B_97) = A_96 ) ),
    inference(resolution,[status(thm)],[c_439,c_18])).

tff(c_5112,plain,(
    ! [A_357,B_358] :
      ( r2_hidden('#skF_2'(A_357,B_358,A_357),B_358)
      | k2_xboole_0(A_357,B_358) = A_357 ) ),
    inference(resolution,[status(thm)],[c_4931,c_495])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5209,plain,(
    ! [A_359,B_360,B_361] :
      ( r2_hidden('#skF_2'(A_359,B_360,A_359),B_361)
      | ~ r1_tarski(B_360,B_361)
      | k2_xboole_0(A_359,B_360) = A_359 ) ),
    inference(resolution,[status(thm)],[c_5112,c_2])).

tff(c_5541,plain,(
    ! [B_371,B_372] :
      ( r2_hidden('#skF_3'(B_371,B_372,B_371),B_371)
      | ~ r1_tarski(B_372,B_371)
      | k2_xboole_0(B_371,B_372) = B_371 ) ),
    inference(resolution,[status(thm)],[c_5209,c_22])).

tff(c_5298,plain,(
    ! [B_361,B_360] :
      ( ~ r2_hidden('#skF_3'(B_361,B_360,B_361),B_361)
      | ~ r1_tarski(B_360,B_361)
      | k2_xboole_0(B_361,B_360) = B_361 ) ),
    inference(resolution,[status(thm)],[c_5209,c_18])).

tff(c_5639,plain,(
    ! [B_373,B_374] :
      ( ~ r1_tarski(B_373,B_374)
      | k2_xboole_0(B_374,B_373) = B_374 ) ),
    inference(resolution,[status(thm)],[c_5541,c_5298])).

tff(c_9466,plain,(
    ! [B_432,B_433,A_434] :
      ( k2_xboole_0(k2_xboole_0(B_432,B_433),A_434) = k2_xboole_0(B_432,B_433)
      | ~ r1_tarski(A_434,B_432) ) ),
    inference(resolution,[status(thm)],[c_116,c_5639])).

tff(c_239,plain,(
    ! [A_1,B_24,A_63] :
      ( ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,k2_xboole_0(A_63,B_24)) ) ),
    inference(resolution,[status(thm)],[c_58,c_212])).

tff(c_12546,plain,(
    ! [A_478,A_479,B_480,B_481] :
      ( ~ r1_tarski(A_478,A_479)
      | r1_tarski(A_478,k2_xboole_0(B_480,B_481))
      | ~ r1_tarski(A_479,B_480) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9466,c_239])).

tff(c_12619,plain,(
    ! [B_482,B_483] :
      ( r1_tarski('#skF_6',k2_xboole_0(B_482,B_483))
      | ~ r1_tarski('#skF_5',B_482) ) ),
    inference(resolution,[status(thm)],[c_28,c_12546])).

tff(c_12681,plain,(
    ! [A_484] :
      ( r1_tarski('#skF_6',A_484)
      | ~ r1_tarski('#skF_5',A_484) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2415,c_12619])).

tff(c_12795,plain,(
    ! [A_485] : r1_tarski('#skF_6',k2_xboole_0(A_485,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_240,c_12681])).

tff(c_5609,plain,(
    ! [B_372,B_371] :
      ( ~ r1_tarski(B_372,B_371)
      | k2_xboole_0(B_371,B_372) = B_371 ) ),
    inference(resolution,[status(thm)],[c_5541,c_5298])).

tff(c_12846,plain,(
    ! [A_485] : k2_xboole_0(k2_xboole_0(A_485,'#skF_5'),'#skF_6') = k2_xboole_0(A_485,'#skF_5') ),
    inference(resolution,[status(thm)],[c_12795,c_5609])).

tff(c_61,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | r2_hidden(D_26,A_28)
      | ~ r2_hidden(D_26,k2_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10248,plain,(
    ! [A_437,B_438,B_439] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_437,B_438),B_439),B_438)
      | r2_hidden('#skF_1'(k2_xboole_0(A_437,B_438),B_439),A_437)
      | r1_tarski(k2_xboole_0(A_437,B_438),B_439) ) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_48,plain,(
    ! [A_20,A_6,B_7] :
      ( r1_tarski(A_20,k2_xboole_0(A_6,B_7))
      | ~ r2_hidden('#skF_1'(A_20,k2_xboole_0(A_6,B_7)),B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_10477,plain,(
    ! [A_437,B_438,A_6] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_437,B_438),k2_xboole_0(A_6,B_438)),A_437)
      | r1_tarski(k2_xboole_0(A_437,B_438),k2_xboole_0(A_6,B_438)) ) ),
    inference(resolution,[status(thm)],[c_10248,c_48])).

tff(c_42068,plain,(
    ! [A_869,A_870,B_871,B_872] :
      ( r1_tarski(A_869,k2_xboole_0(k2_xboole_0(A_870,B_871),B_872))
      | ~ r2_hidden('#skF_1'(A_869,k2_xboole_0(k2_xboole_0(A_870,B_871),B_872)),A_870) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_42424,plain,(
    ! [A_873,B_874,B_875] : r1_tarski(k2_xboole_0(A_873,B_874),k2_xboole_0(k2_xboole_0(A_873,B_875),B_874)) ),
    inference(resolution,[status(thm)],[c_10477,c_42068])).

tff(c_42791,plain,(
    ! [A_876] : r1_tarski(k2_xboole_0(A_876,'#skF_6'),k2_xboole_0(A_876,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12846,c_42424])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35458,plain,(
    ! [A_831,B_832] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_831,B_832),B_832),A_831)
      | r1_tarski(k2_xboole_0(A_831,B_832),B_832) ) ),
    inference(resolution,[status(thm)],[c_10248,c_4])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5736,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_5639])).

tff(c_5969,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,k2_xboole_0('#skF_5','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_20,'#skF_5'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5736,c_48])).

tff(c_6007,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_20,'#skF_5'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5736,c_5969])).

tff(c_35604,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_35458,c_6007])).

tff(c_35914,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_35604,c_5609])).

tff(c_36643,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,k2_xboole_0('#skF_4','#skF_5'))
      | r1_tarski(A_1,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35914,c_239])).

tff(c_42799,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_42791,c_36643])).

tff(c_42951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_42799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:23:26 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.35/9.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.35/9.12  
% 19.35/9.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.35/9.12  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 19.35/9.12  
% 19.35/9.12  %Foreground sorts:
% 19.35/9.12  
% 19.35/9.12  
% 19.35/9.12  %Background operators:
% 19.35/9.12  
% 19.35/9.12  
% 19.35/9.12  %Foreground operators:
% 19.35/9.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.35/9.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.35/9.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.35/9.12  tff('#skF_5', type, '#skF_5': $i).
% 19.35/9.12  tff('#skF_6', type, '#skF_6': $i).
% 19.35/9.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.35/9.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.35/9.12  tff('#skF_4', type, '#skF_4': $i).
% 19.35/9.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 19.35/9.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.35/9.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.35/9.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.35/9.12  
% 19.35/9.13  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 19.35/9.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.35/9.13  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 19.35/9.13  tff(c_26, plain, (~r1_tarski(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.35/9.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.35/9.13  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_34, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.35/9.13  tff(c_212, plain, (![A_62, A_63, B_64]: (r1_tarski(A_62, k2_xboole_0(A_63, B_64)) | ~r2_hidden('#skF_1'(A_62, k2_xboole_0(A_63, B_64)), B_64))), inference(resolution, [status(thm)], [c_10, c_34])).
% 19.35/9.13  tff(c_240, plain, (![A_1, A_63]: (r1_tarski(A_1, k2_xboole_0(A_63, A_1)))), inference(resolution, [status(thm)], [c_6, c_212])).
% 19.35/9.13  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_2301, plain, (![A_240, C_241]: (r2_hidden('#skF_3'(A_240, A_240, C_241), C_241) | k2_xboole_0(A_240, A_240)=C_241 | r2_hidden('#skF_2'(A_240, A_240, C_241), A_240))), inference(factorization, [status(thm), theory('equality')], [c_24])).
% 19.35/9.13  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_2382, plain, (![A_242]: (r2_hidden('#skF_3'(A_242, A_242, A_242), A_242) | k2_xboole_0(A_242, A_242)=A_242)), inference(resolution, [status(thm)], [c_2301, c_22])).
% 19.35/9.13  tff(c_20, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_1181, plain, (![B_170, C_171]: (~r2_hidden('#skF_3'(B_170, B_170, C_171), B_170) | k2_xboole_0(B_170, B_170)=C_171 | r2_hidden('#skF_2'(B_170, B_170, C_171), B_170))), inference(factorization, [status(thm), theory('equality')], [c_20])).
% 19.35/9.13  tff(c_18, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_1210, plain, (![B_170]: (~r2_hidden('#skF_3'(B_170, B_170, B_170), B_170) | k2_xboole_0(B_170, B_170)=B_170)), inference(resolution, [status(thm)], [c_1181, c_18])).
% 19.35/9.13  tff(c_2415, plain, (![A_242]: (k2_xboole_0(A_242, A_242)=A_242)), inference(resolution, [status(thm)], [c_2382, c_1210])).
% 19.35/9.13  tff(c_28, plain, (r1_tarski('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.35/9.13  tff(c_51, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.35/9.13  tff(c_58, plain, (![A_1, B_2, B_24]: (r2_hidden('#skF_1'(A_1, B_2), B_24) | ~r1_tarski(A_1, B_24) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_51])).
% 19.35/9.13  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_99, plain, (![A_40, A_41, B_42]: (r1_tarski(A_40, k2_xboole_0(A_41, B_42)) | ~r2_hidden('#skF_1'(A_40, k2_xboole_0(A_41, B_42)), A_41))), inference(resolution, [status(thm)], [c_12, c_34])).
% 19.35/9.13  tff(c_116, plain, (![A_1, B_24, B_42]: (~r1_tarski(A_1, B_24) | r1_tarski(A_1, k2_xboole_0(B_24, B_42)))), inference(resolution, [status(thm)], [c_58, c_99])).
% 19.35/9.13  tff(c_881, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_2'(A_142, B_143, C_144), B_143) | r2_hidden('#skF_2'(A_142, B_143, C_144), A_142) | r2_hidden('#skF_3'(A_142, B_143, C_144), C_144) | k2_xboole_0(A_142, B_143)=C_144)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_4931, plain, (![A_355, B_356]: (r2_hidden('#skF_2'(A_355, B_356, A_355), B_356) | r2_hidden('#skF_3'(A_355, B_356, A_355), A_355) | k2_xboole_0(A_355, B_356)=A_355)), inference(resolution, [status(thm)], [c_881, c_22])).
% 19.35/9.13  tff(c_439, plain, (![A_96, B_97, C_98]: (r2_hidden('#skF_2'(A_96, B_97, C_98), B_97) | r2_hidden('#skF_2'(A_96, B_97, C_98), A_96) | ~r2_hidden('#skF_3'(A_96, B_97, C_98), A_96) | k2_xboole_0(A_96, B_97)=C_98)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_495, plain, (![A_96, B_97]: (r2_hidden('#skF_2'(A_96, B_97, A_96), B_97) | ~r2_hidden('#skF_3'(A_96, B_97, A_96), A_96) | k2_xboole_0(A_96, B_97)=A_96)), inference(resolution, [status(thm)], [c_439, c_18])).
% 19.35/9.13  tff(c_5112, plain, (![A_357, B_358]: (r2_hidden('#skF_2'(A_357, B_358, A_357), B_358) | k2_xboole_0(A_357, B_358)=A_357)), inference(resolution, [status(thm)], [c_4931, c_495])).
% 19.35/9.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.35/9.13  tff(c_5209, plain, (![A_359, B_360, B_361]: (r2_hidden('#skF_2'(A_359, B_360, A_359), B_361) | ~r1_tarski(B_360, B_361) | k2_xboole_0(A_359, B_360)=A_359)), inference(resolution, [status(thm)], [c_5112, c_2])).
% 19.35/9.13  tff(c_5541, plain, (![B_371, B_372]: (r2_hidden('#skF_3'(B_371, B_372, B_371), B_371) | ~r1_tarski(B_372, B_371) | k2_xboole_0(B_371, B_372)=B_371)), inference(resolution, [status(thm)], [c_5209, c_22])).
% 19.35/9.13  tff(c_5298, plain, (![B_361, B_360]: (~r2_hidden('#skF_3'(B_361, B_360, B_361), B_361) | ~r1_tarski(B_360, B_361) | k2_xboole_0(B_361, B_360)=B_361)), inference(resolution, [status(thm)], [c_5209, c_18])).
% 19.35/9.13  tff(c_5639, plain, (![B_373, B_374]: (~r1_tarski(B_373, B_374) | k2_xboole_0(B_374, B_373)=B_374)), inference(resolution, [status(thm)], [c_5541, c_5298])).
% 19.35/9.13  tff(c_9466, plain, (![B_432, B_433, A_434]: (k2_xboole_0(k2_xboole_0(B_432, B_433), A_434)=k2_xboole_0(B_432, B_433) | ~r1_tarski(A_434, B_432))), inference(resolution, [status(thm)], [c_116, c_5639])).
% 19.35/9.13  tff(c_239, plain, (![A_1, B_24, A_63]: (~r1_tarski(A_1, B_24) | r1_tarski(A_1, k2_xboole_0(A_63, B_24)))), inference(resolution, [status(thm)], [c_58, c_212])).
% 19.35/9.13  tff(c_12546, plain, (![A_478, A_479, B_480, B_481]: (~r1_tarski(A_478, A_479) | r1_tarski(A_478, k2_xboole_0(B_480, B_481)) | ~r1_tarski(A_479, B_480))), inference(superposition, [status(thm), theory('equality')], [c_9466, c_239])).
% 19.35/9.13  tff(c_12619, plain, (![B_482, B_483]: (r1_tarski('#skF_6', k2_xboole_0(B_482, B_483)) | ~r1_tarski('#skF_5', B_482))), inference(resolution, [status(thm)], [c_28, c_12546])).
% 19.35/9.13  tff(c_12681, plain, (![A_484]: (r1_tarski('#skF_6', A_484) | ~r1_tarski('#skF_5', A_484))), inference(superposition, [status(thm), theory('equality')], [c_2415, c_12619])).
% 19.35/9.13  tff(c_12795, plain, (![A_485]: (r1_tarski('#skF_6', k2_xboole_0(A_485, '#skF_5')))), inference(resolution, [status(thm)], [c_240, c_12681])).
% 19.35/9.13  tff(c_5609, plain, (![B_372, B_371]: (~r1_tarski(B_372, B_371) | k2_xboole_0(B_371, B_372)=B_371)), inference(resolution, [status(thm)], [c_5541, c_5298])).
% 19.35/9.13  tff(c_12846, plain, (![A_485]: (k2_xboole_0(k2_xboole_0(A_485, '#skF_5'), '#skF_6')=k2_xboole_0(A_485, '#skF_5'))), inference(resolution, [status(thm)], [c_12795, c_5609])).
% 19.35/9.13  tff(c_61, plain, (![D_26, B_27, A_28]: (r2_hidden(D_26, B_27) | r2_hidden(D_26, A_28) | ~r2_hidden(D_26, k2_xboole_0(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.35/9.13  tff(c_10248, plain, (![A_437, B_438, B_439]: (r2_hidden('#skF_1'(k2_xboole_0(A_437, B_438), B_439), B_438) | r2_hidden('#skF_1'(k2_xboole_0(A_437, B_438), B_439), A_437) | r1_tarski(k2_xboole_0(A_437, B_438), B_439))), inference(resolution, [status(thm)], [c_6, c_61])).
% 19.35/9.13  tff(c_48, plain, (![A_20, A_6, B_7]: (r1_tarski(A_20, k2_xboole_0(A_6, B_7)) | ~r2_hidden('#skF_1'(A_20, k2_xboole_0(A_6, B_7)), B_7))), inference(resolution, [status(thm)], [c_10, c_34])).
% 19.35/9.13  tff(c_10477, plain, (![A_437, B_438, A_6]: (r2_hidden('#skF_1'(k2_xboole_0(A_437, B_438), k2_xboole_0(A_6, B_438)), A_437) | r1_tarski(k2_xboole_0(A_437, B_438), k2_xboole_0(A_6, B_438)))), inference(resolution, [status(thm)], [c_10248, c_48])).
% 19.35/9.13  tff(c_42068, plain, (![A_869, A_870, B_871, B_872]: (r1_tarski(A_869, k2_xboole_0(k2_xboole_0(A_870, B_871), B_872)) | ~r2_hidden('#skF_1'(A_869, k2_xboole_0(k2_xboole_0(A_870, B_871), B_872)), A_870))), inference(resolution, [status(thm)], [c_12, c_99])).
% 19.35/9.13  tff(c_42424, plain, (![A_873, B_874, B_875]: (r1_tarski(k2_xboole_0(A_873, B_874), k2_xboole_0(k2_xboole_0(A_873, B_875), B_874)))), inference(resolution, [status(thm)], [c_10477, c_42068])).
% 19.35/9.13  tff(c_42791, plain, (![A_876]: (r1_tarski(k2_xboole_0(A_876, '#skF_6'), k2_xboole_0(A_876, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_12846, c_42424])).
% 19.35/9.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.35/9.13  tff(c_35458, plain, (![A_831, B_832]: (r2_hidden('#skF_1'(k2_xboole_0(A_831, B_832), B_832), A_831) | r1_tarski(k2_xboole_0(A_831, B_832), B_832))), inference(resolution, [status(thm)], [c_10248, c_4])).
% 19.35/9.13  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.35/9.13  tff(c_5736, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_30, c_5639])).
% 19.35/9.13  tff(c_5969, plain, (![A_20]: (r1_tarski(A_20, k2_xboole_0('#skF_5', '#skF_4')) | ~r2_hidden('#skF_1'(A_20, '#skF_5'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5736, c_48])).
% 19.35/9.13  tff(c_6007, plain, (![A_20]: (r1_tarski(A_20, '#skF_5') | ~r2_hidden('#skF_1'(A_20, '#skF_5'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5736, c_5969])).
% 19.35/9.13  tff(c_35604, plain, (r1_tarski(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_35458, c_6007])).
% 19.35/9.13  tff(c_35914, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_35604, c_5609])).
% 19.35/9.13  tff(c_36643, plain, (![A_1]: (~r1_tarski(A_1, k2_xboole_0('#skF_4', '#skF_5')) | r1_tarski(A_1, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35914, c_239])).
% 19.35/9.13  tff(c_42799, plain, (r1_tarski(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_42791, c_36643])).
% 19.35/9.13  tff(c_42951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_42799])).
% 19.35/9.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.35/9.13  
% 19.35/9.13  Inference rules
% 19.35/9.13  ----------------------
% 19.35/9.13  #Ref     : 0
% 19.35/9.13  #Sup     : 11562
% 19.35/9.13  #Fact    : 46
% 19.35/9.13  #Define  : 0
% 19.35/9.13  #Split   : 2
% 19.35/9.13  #Chain   : 0
% 19.35/9.13  #Close   : 0
% 19.35/9.13  
% 19.35/9.13  Ordering : KBO
% 19.35/9.13  
% 19.35/9.13  Simplification rules
% 19.35/9.13  ----------------------
% 19.35/9.13  #Subsume      : 3312
% 19.35/9.13  #Demod        : 4284
% 19.35/9.13  #Tautology    : 2212
% 19.35/9.13  #SimpNegUnit  : 5
% 19.35/9.13  #BackRed      : 2
% 19.35/9.13  
% 19.35/9.13  #Partial instantiations: 0
% 19.35/9.13  #Strategies tried      : 1
% 19.35/9.13  
% 19.35/9.13  Timing (in seconds)
% 19.35/9.13  ----------------------
% 19.35/9.14  Preprocessing        : 0.27
% 19.35/9.14  Parsing              : 0.14
% 19.35/9.14  CNF conversion       : 0.02
% 19.35/9.14  Main loop            : 8.12
% 19.35/9.14  Inferencing          : 1.14
% 19.35/9.14  Reduction            : 2.00
% 19.35/9.14  Demodulation         : 1.58
% 19.35/9.14  BG Simplification    : 0.15
% 19.35/9.14  Subsumption          : 4.36
% 19.35/9.14  Abstraction          : 0.23
% 19.35/9.14  MUC search           : 0.00
% 19.35/9.14  Cooper               : 0.00
% 19.35/9.14  Total                : 8.42
% 19.35/9.14  Index Insertion      : 0.00
% 19.35/9.14  Index Deletion       : 0.00
% 19.35/9.14  Index Matching       : 0.00
% 19.35/9.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
