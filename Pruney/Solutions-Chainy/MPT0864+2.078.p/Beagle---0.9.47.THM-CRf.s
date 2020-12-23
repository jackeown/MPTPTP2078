%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:19 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 163 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 214 expanded)
%              Number of equality atoms :   73 ( 184 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_536,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_548,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_536])).

tff(c_552,plain,(
    ! [A_101] : k4_xboole_0(A_101,k1_xboole_0) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_548])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_558,plain,(
    ! [A_101] : k4_xboole_0(A_101,A_101) = k3_xboole_0(A_101,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_8])).

tff(c_563,plain,(
    ! [A_101] : k4_xboole_0(A_101,A_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_558])).

tff(c_20,plain,(
    ! [B_20] : k4_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_tarski(B_20) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_574,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_20])).

tff(c_34,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_1'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_614,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(k1_tarski(A_107),k1_tarski(B_108)) = k1_tarski(A_107)
      | B_108 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( ~ r2_hidden(B_22,A_21)
      | k4_xboole_0(A_21,k1_tarski(B_22)) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_670,plain,(
    ! [B_110,A_111] :
      ( ~ r2_hidden(B_110,k1_tarski(A_111))
      | B_110 = A_111 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_24])).

tff(c_677,plain,(
    ! [A_111] :
      ( '#skF_1'(k1_tarski(A_111)) = A_111
      | k1_tarski(A_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_670])).

tff(c_682,plain,(
    ! [A_111] : '#skF_1'(k1_tarski(A_111)) = A_111 ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_677])).

tff(c_498,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,k1_tarski(B_93)) = A_92
      | r2_hidden(B_93,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_510,plain,(
    ! [B_93] : r2_hidden(B_93,k1_tarski(B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_20])).

tff(c_733,plain,(
    ! [D_118,A_119,C_120] :
      ( ~ r2_hidden(D_118,A_119)
      | k4_tarski(C_120,D_118) != '#skF_1'(A_119)
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_735,plain,(
    ! [C_120,B_93] :
      ( k4_tarski(C_120,B_93) != '#skF_1'(k1_tarski(B_93))
      | k1_tarski(B_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_510,c_733])).

tff(c_739,plain,(
    ! [C_120,B_93] :
      ( k4_tarski(C_120,B_93) != B_93
      | k1_tarski(B_93) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_735])).

tff(c_740,plain,(
    ! [C_120,B_93] : k4_tarski(C_120,B_93) != B_93 ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_739])).

tff(c_223,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_235,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_223])).

tff(c_239,plain,(
    ! [A_63] : k4_xboole_0(A_63,k1_xboole_0) = A_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_235])).

tff(c_245,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k3_xboole_0(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_8])).

tff(c_250,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_245])).

tff(c_261,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_20])).

tff(c_301,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k1_tarski(A_69),k1_tarski(B_70)) = k1_tarski(A_69)
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_357,plain,(
    ! [B_72,A_73] :
      ( ~ r2_hidden(B_72,k1_tarski(A_73))
      | B_72 = A_73 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_24])).

tff(c_364,plain,(
    ! [A_73] :
      ( '#skF_1'(k1_tarski(A_73)) = A_73
      | k1_tarski(A_73) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_357])).

tff(c_369,plain,(
    ! [A_73] : '#skF_1'(k1_tarski(A_73)) = A_73 ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_364])).

tff(c_200,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,k1_tarski(B_57)) = A_56
      | r2_hidden(B_57,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_215,plain,(
    ! [B_57] : r2_hidden(B_57,k1_tarski(B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_20])).

tff(c_420,plain,(
    ! [C_80,A_81,D_82] :
      ( ~ r2_hidden(C_80,A_81)
      | k4_tarski(C_80,D_82) != '#skF_1'(A_81)
      | k1_xboole_0 = A_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_422,plain,(
    ! [B_57,D_82] :
      ( k4_tarski(B_57,D_82) != '#skF_1'(k1_tarski(B_57))
      | k1_tarski(B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_215,c_420])).

tff(c_426,plain,(
    ! [B_57,D_82] :
      ( k4_tarski(B_57,D_82) != B_57
      | k1_tarski(B_57) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_422])).

tff(c_427,plain,(
    ! [B_57,D_82] : k4_tarski(B_57,D_82) != B_57 ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_426])).

tff(c_42,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_107,plain,(
    ! [A_45,B_46] : k1_mcart_1(k4_tarski(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_107])).

tff(c_91,plain,(
    ! [A_43,B_44] : k2_mcart_1(k4_tarski(A_43,B_44)) = B_44 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_91])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_100,c_40])).

tff(c_124,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_127,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_42])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_127])).

tff(c_435,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_439,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_42])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.51/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.51/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.38  
% 2.80/1.40  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.80/1.40  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.80/1.40  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.40  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.80/1.40  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.80/1.40  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.80/1.40  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.80/1.40  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.80/1.40  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.80/1.40  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.40  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.40  tff(c_536, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.40  tff(c_548, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_536])).
% 2.80/1.40  tff(c_552, plain, (![A_101]: (k4_xboole_0(A_101, k1_xboole_0)=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_548])).
% 2.80/1.40  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.40  tff(c_558, plain, (![A_101]: (k4_xboole_0(A_101, A_101)=k3_xboole_0(A_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_552, c_8])).
% 2.80/1.40  tff(c_563, plain, (![A_101]: (k4_xboole_0(A_101, A_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_558])).
% 2.80/1.40  tff(c_20, plain, (![B_20]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_tarski(B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.40  tff(c_574, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_563, c_20])).
% 2.80/1.40  tff(c_34, plain, (![A_27]: (r2_hidden('#skF_1'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_614, plain, (![A_107, B_108]: (k4_xboole_0(k1_tarski(A_107), k1_tarski(B_108))=k1_tarski(A_107) | B_108=A_107)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.40  tff(c_24, plain, (![B_22, A_21]: (~r2_hidden(B_22, A_21) | k4_xboole_0(A_21, k1_tarski(B_22))!=A_21)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.40  tff(c_670, plain, (![B_110, A_111]: (~r2_hidden(B_110, k1_tarski(A_111)) | B_110=A_111)), inference(superposition, [status(thm), theory('equality')], [c_614, c_24])).
% 2.80/1.40  tff(c_677, plain, (![A_111]: ('#skF_1'(k1_tarski(A_111))=A_111 | k1_tarski(A_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_670])).
% 2.80/1.40  tff(c_682, plain, (![A_111]: ('#skF_1'(k1_tarski(A_111))=A_111)), inference(negUnitSimplification, [status(thm)], [c_574, c_677])).
% 2.80/1.40  tff(c_498, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k1_tarski(B_93))=A_92 | r2_hidden(B_93, A_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.40  tff(c_510, plain, (![B_93]: (r2_hidden(B_93, k1_tarski(B_93)))), inference(superposition, [status(thm), theory('equality')], [c_498, c_20])).
% 2.80/1.40  tff(c_733, plain, (![D_118, A_119, C_120]: (~r2_hidden(D_118, A_119) | k4_tarski(C_120, D_118)!='#skF_1'(A_119) | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_735, plain, (![C_120, B_93]: (k4_tarski(C_120, B_93)!='#skF_1'(k1_tarski(B_93)) | k1_tarski(B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_510, c_733])).
% 2.80/1.40  tff(c_739, plain, (![C_120, B_93]: (k4_tarski(C_120, B_93)!=B_93 | k1_tarski(B_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_682, c_735])).
% 2.80/1.40  tff(c_740, plain, (![C_120, B_93]: (k4_tarski(C_120, B_93)!=B_93)), inference(negUnitSimplification, [status(thm)], [c_574, c_739])).
% 2.80/1.40  tff(c_223, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.40  tff(c_235, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_223])).
% 2.80/1.40  tff(c_239, plain, (![A_63]: (k4_xboole_0(A_63, k1_xboole_0)=A_63)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_235])).
% 2.80/1.40  tff(c_245, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k3_xboole_0(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_239, c_8])).
% 2.80/1.40  tff(c_250, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_245])).
% 2.80/1.40  tff(c_261, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_20])).
% 2.80/1.40  tff(c_301, plain, (![A_69, B_70]: (k4_xboole_0(k1_tarski(A_69), k1_tarski(B_70))=k1_tarski(A_69) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.40  tff(c_357, plain, (![B_72, A_73]: (~r2_hidden(B_72, k1_tarski(A_73)) | B_72=A_73)), inference(superposition, [status(thm), theory('equality')], [c_301, c_24])).
% 2.80/1.40  tff(c_364, plain, (![A_73]: ('#skF_1'(k1_tarski(A_73))=A_73 | k1_tarski(A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_357])).
% 2.80/1.40  tff(c_369, plain, (![A_73]: ('#skF_1'(k1_tarski(A_73))=A_73)), inference(negUnitSimplification, [status(thm)], [c_261, c_364])).
% 2.80/1.40  tff(c_200, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k1_tarski(B_57))=A_56 | r2_hidden(B_57, A_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.40  tff(c_215, plain, (![B_57]: (r2_hidden(B_57, k1_tarski(B_57)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_20])).
% 2.80/1.40  tff(c_420, plain, (![C_80, A_81, D_82]: (~r2_hidden(C_80, A_81) | k4_tarski(C_80, D_82)!='#skF_1'(A_81) | k1_xboole_0=A_81)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.40  tff(c_422, plain, (![B_57, D_82]: (k4_tarski(B_57, D_82)!='#skF_1'(k1_tarski(B_57)) | k1_tarski(B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_215, c_420])).
% 2.80/1.40  tff(c_426, plain, (![B_57, D_82]: (k4_tarski(B_57, D_82)!=B_57 | k1_tarski(B_57)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_422])).
% 2.80/1.40  tff(c_427, plain, (![B_57, D_82]: (k4_tarski(B_57, D_82)!=B_57)), inference(negUnitSimplification, [status(thm)], [c_261, c_426])).
% 2.80/1.40  tff(c_42, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.40  tff(c_107, plain, (![A_45, B_46]: (k1_mcart_1(k4_tarski(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.40  tff(c_116, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_42, c_107])).
% 2.80/1.40  tff(c_91, plain, (![A_43, B_44]: (k2_mcart_1(k4_tarski(A_43, B_44))=B_44)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.40  tff(c_100, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_42, c_91])).
% 2.80/1.40  tff(c_40, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.40  tff(c_123, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_100, c_40])).
% 2.80/1.40  tff(c_124, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_123])).
% 2.80/1.40  tff(c_127, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_42])).
% 2.80/1.40  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_127])).
% 2.80/1.40  tff(c_435, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_123])).
% 2.80/1.40  tff(c_439, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_42])).
% 2.80/1.40  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_740, c_439])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 162
% 2.80/1.40  #Fact    : 0
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 1
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 5
% 2.80/1.40  #Demod        : 43
% 2.80/1.40  #Tautology    : 124
% 2.80/1.40  #SimpNegUnit  : 18
% 2.80/1.40  #BackRed      : 10
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.40  Preprocessing        : 0.32
% 2.80/1.40  Parsing              : 0.17
% 2.80/1.40  CNF conversion       : 0.02
% 2.80/1.40  Main loop            : 0.26
% 2.80/1.40  Inferencing          : 0.11
% 2.80/1.40  Reduction            : 0.08
% 2.80/1.40  Demodulation         : 0.05
% 2.80/1.40  BG Simplification    : 0.02
% 2.80/1.40  Subsumption          : 0.03
% 2.80/1.40  Abstraction          : 0.02
% 2.80/1.40  MUC search           : 0.00
% 2.80/1.40  Cooper               : 0.00
% 2.80/1.40  Total                : 0.61
% 2.80/1.40  Index Insertion      : 0.00
% 2.80/1.40  Index Deletion       : 0.00
% 2.80/1.40  Index Matching       : 0.00
% 2.80/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
