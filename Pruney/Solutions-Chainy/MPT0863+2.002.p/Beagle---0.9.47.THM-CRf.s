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
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 160 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 334 expanded)
%              Number of equality atoms :   34 ( 134 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_64,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_66,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_81,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_137,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(k2_mcart_1(A_54),C_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_140,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_28,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_825,plain,(
    ! [A_1208,B_1209,C_1210] :
      ( k4_xboole_0(k2_tarski(A_1208,B_1209),C_1210) = k2_tarski(A_1208,B_1209)
      | r2_hidden(B_1209,C_1210)
      | r2_hidden(A_1208,C_1210) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1467,plain,(
    ! [D_1656,C_1657,A_1658,B_1659] :
      ( ~ r2_hidden(D_1656,C_1657)
      | ~ r2_hidden(D_1656,k2_tarski(A_1658,B_1659))
      | r2_hidden(B_1659,C_1657)
      | r2_hidden(A_1658,C_1657) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_4])).

tff(c_1525,plain,(
    ! [C_1686,A_1687,B_1688] :
      ( ~ r2_hidden(C_1686,k2_tarski(A_1687,B_1688))
      | r2_hidden(B_1688,k1_tarski(C_1686))
      | r2_hidden(A_1687,k1_tarski(C_1686)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1467])).

tff(c_1594,plain,
    ( r2_hidden('#skF_9',k1_tarski(k2_mcart_1('#skF_5')))
    | r2_hidden('#skF_8',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_140,c_1525])).

tff(c_1800,plain,(
    r2_hidden('#skF_8',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1594])).

tff(c_26,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1817,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1800,c_26])).

tff(c_1879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1817])).

tff(c_1880,plain,(
    r2_hidden('#skF_9',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1594])).

tff(c_1898,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1880,c_26])).

tff(c_1960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1898])).

tff(c_1962,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1975,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_62])).

tff(c_1961,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2038,plain,(
    ! [A_1931,B_1932,C_1933] :
      ( r2_hidden(k1_mcart_1(A_1931),B_1932)
      | ~ r2_hidden(A_1931,k2_zfmisc_1(B_1932,C_1933)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2041,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_2038])).

tff(c_2707,plain,(
    ! [A_3067,B_3068,C_3069] :
      ( k4_xboole_0(k2_tarski(A_3067,B_3068),C_3069) = k2_tarski(A_3067,B_3068)
      | r2_hidden(B_3068,C_3069)
      | r2_hidden(A_3067,C_3069) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3009,plain,(
    ! [D_3376,C_3377,A_3378,B_3379] :
      ( ~ r2_hidden(D_3376,C_3377)
      | ~ r2_hidden(D_3376,k2_tarski(A_3378,B_3379))
      | r2_hidden(B_3379,C_3377)
      | r2_hidden(A_3378,C_3377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2707,c_4])).

tff(c_3294,plain,(
    ! [C_3491,A_3492,B_3493] :
      ( ~ r2_hidden(C_3491,k2_tarski(A_3492,B_3493))
      | r2_hidden(B_3493,k1_tarski(C_3491))
      | r2_hidden(A_3492,k1_tarski(C_3491)) ) ),
    inference(resolution,[status(thm)],[c_28,c_3009])).

tff(c_3360,plain,
    ( r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5')))
    | r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_2041,c_3294])).

tff(c_3394,plain,(
    r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_3360])).

tff(c_3411,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3394,c_26])).

tff(c_3472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1961,c_3411])).

tff(c_3473,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3360])).

tff(c_3491,plain,(
    k1_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3473,c_26])).

tff(c_3552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1975,c_3491])).

tff(c_3553,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3554,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3560,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3554,c_68])).

tff(c_3631,plain,(
    ! [A_3626,B_3627,C_3628] :
      ( r2_hidden(k1_mcart_1(A_3626),B_3627)
      | ~ r2_hidden(A_3626,k2_zfmisc_1(B_3627,C_3628)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3634,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_3631])).

tff(c_4300,plain,(
    ! [A_4736,B_4737,C_4738] :
      ( k4_xboole_0(k2_tarski(A_4736,B_4737),C_4738) = k2_tarski(A_4736,B_4737)
      | r2_hidden(B_4737,C_4738)
      | r2_hidden(A_4736,C_4738) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4903,plain,(
    ! [D_5130,C_5131,A_5132,B_5133] :
      ( ~ r2_hidden(D_5130,C_5131)
      | ~ r2_hidden(D_5130,k2_tarski(A_5132,B_5133))
      | r2_hidden(B_5133,C_5131)
      | r2_hidden(A_5132,C_5131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4300,c_4])).

tff(c_4987,plain,(
    ! [C_5187,A_5188,B_5189] :
      ( ~ r2_hidden(C_5187,k2_tarski(A_5188,B_5189))
      | r2_hidden(B_5189,k1_tarski(C_5187))
      | r2_hidden(A_5188,k1_tarski(C_5187)) ) ),
    inference(resolution,[status(thm)],[c_28,c_4903])).

tff(c_5053,plain,
    ( r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5')))
    | r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3634,c_4987])).

tff(c_5058,plain,(
    r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_5053])).

tff(c_5075,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5058,c_26])).

tff(c_5136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3560,c_5075])).

tff(c_5137,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_5053])).

tff(c_5155,plain,(
    k1_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5137,c_26])).

tff(c_5216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3553,c_5155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:50:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/2.01  
% 4.90/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/2.01  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 4.90/2.01  
% 4.90/2.01  %Foreground sorts:
% 4.90/2.01  
% 4.90/2.01  
% 4.90/2.01  %Background operators:
% 4.90/2.01  
% 4.90/2.01  
% 4.90/2.01  %Foreground operators:
% 4.90/2.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.90/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.90/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.90/2.01  tff('#skF_7', type, '#skF_7': $i).
% 4.90/2.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.90/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.90/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.90/2.01  tff('#skF_5', type, '#skF_5': $i).
% 4.90/2.01  tff('#skF_6', type, '#skF_6': $i).
% 4.90/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.90/2.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.90/2.01  tff('#skF_9', type, '#skF_9': $i).
% 4.90/2.01  tff('#skF_8', type, '#skF_8': $i).
% 4.90/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/2.01  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.90/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.90/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/2.01  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.90/2.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.90/2.01  
% 4.90/2.02  tff(f_85, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_mcart_1)).
% 4.90/2.02  tff(f_74, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.90/2.02  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.90/2.02  tff(f_68, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 4.90/2.02  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.90/2.02  tff(c_64, plain, (k1_mcart_1('#skF_5')!='#skF_6' | k2_mcart_1('#skF_5')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.90/2.02  tff(c_82, plain, (k2_mcart_1('#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_64])).
% 4.90/2.02  tff(c_66, plain, (k1_mcart_1('#skF_5')!='#skF_7' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.90/2.02  tff(c_81, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitLeft, [status(thm)], [c_66])).
% 4.90/2.02  tff(c_60, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.90/2.02  tff(c_137, plain, (![A_54, C_55, B_56]: (r2_hidden(k2_mcart_1(A_54), C_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_140, plain, (r2_hidden(k2_mcart_1('#skF_5'), k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_60, c_137])).
% 4.90/2.02  tff(c_28, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.90/2.02  tff(c_825, plain, (![A_1208, B_1209, C_1210]: (k4_xboole_0(k2_tarski(A_1208, B_1209), C_1210)=k2_tarski(A_1208, B_1209) | r2_hidden(B_1209, C_1210) | r2_hidden(A_1208, C_1210))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.90/2.02  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.90/2.02  tff(c_1467, plain, (![D_1656, C_1657, A_1658, B_1659]: (~r2_hidden(D_1656, C_1657) | ~r2_hidden(D_1656, k2_tarski(A_1658, B_1659)) | r2_hidden(B_1659, C_1657) | r2_hidden(A_1658, C_1657))), inference(superposition, [status(thm), theory('equality')], [c_825, c_4])).
% 4.90/2.02  tff(c_1525, plain, (![C_1686, A_1687, B_1688]: (~r2_hidden(C_1686, k2_tarski(A_1687, B_1688)) | r2_hidden(B_1688, k1_tarski(C_1686)) | r2_hidden(A_1687, k1_tarski(C_1686)))), inference(resolution, [status(thm)], [c_28, c_1467])).
% 4.90/2.02  tff(c_1594, plain, (r2_hidden('#skF_9', k1_tarski(k2_mcart_1('#skF_5'))) | r2_hidden('#skF_8', k1_tarski(k2_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_140, c_1525])).
% 4.90/2.02  tff(c_1800, plain, (r2_hidden('#skF_8', k1_tarski(k2_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_1594])).
% 4.90/2.02  tff(c_26, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.90/2.02  tff(c_1817, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_1800, c_26])).
% 4.90/2.02  tff(c_1879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_1817])).
% 4.90/2.02  tff(c_1880, plain, (r2_hidden('#skF_9', k1_tarski(k2_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1594])).
% 4.90/2.02  tff(c_1898, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_1880, c_26])).
% 4.90/2.02  tff(c_1960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1898])).
% 4.90/2.02  tff(c_1962, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(splitRight, [status(thm)], [c_64])).
% 4.90/2.02  tff(c_62, plain, (k1_mcart_1('#skF_5')!='#skF_7' | k2_mcart_1('#skF_5')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.90/2.02  tff(c_1975, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1962, c_62])).
% 4.90/2.02  tff(c_1961, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 4.90/2.02  tff(c_2038, plain, (![A_1931, B_1932, C_1933]: (r2_hidden(k1_mcart_1(A_1931), B_1932) | ~r2_hidden(A_1931, k2_zfmisc_1(B_1932, C_1933)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_2041, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_2038])).
% 4.90/2.02  tff(c_2707, plain, (![A_3067, B_3068, C_3069]: (k4_xboole_0(k2_tarski(A_3067, B_3068), C_3069)=k2_tarski(A_3067, B_3068) | r2_hidden(B_3068, C_3069) | r2_hidden(A_3067, C_3069))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.90/2.02  tff(c_3009, plain, (![D_3376, C_3377, A_3378, B_3379]: (~r2_hidden(D_3376, C_3377) | ~r2_hidden(D_3376, k2_tarski(A_3378, B_3379)) | r2_hidden(B_3379, C_3377) | r2_hidden(A_3378, C_3377))), inference(superposition, [status(thm), theory('equality')], [c_2707, c_4])).
% 4.90/2.02  tff(c_3294, plain, (![C_3491, A_3492, B_3493]: (~r2_hidden(C_3491, k2_tarski(A_3492, B_3493)) | r2_hidden(B_3493, k1_tarski(C_3491)) | r2_hidden(A_3492, k1_tarski(C_3491)))), inference(resolution, [status(thm)], [c_28, c_3009])).
% 4.90/2.02  tff(c_3360, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5'))) | r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_2041, c_3294])).
% 4.90/2.02  tff(c_3394, plain, (r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_3360])).
% 4.90/2.02  tff(c_3411, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3394, c_26])).
% 4.90/2.02  tff(c_3472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1961, c_3411])).
% 4.90/2.02  tff(c_3473, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_3360])).
% 4.90/2.02  tff(c_3491, plain, (k1_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_3473, c_26])).
% 4.90/2.02  tff(c_3552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1975, c_3491])).
% 4.90/2.02  tff(c_3553, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 4.90/2.02  tff(c_3554, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 4.90/2.02  tff(c_68, plain, (k1_mcart_1('#skF_5')!='#skF_6' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.90/2.02  tff(c_3560, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3554, c_68])).
% 4.90/2.02  tff(c_3631, plain, (![A_3626, B_3627, C_3628]: (r2_hidden(k1_mcart_1(A_3626), B_3627) | ~r2_hidden(A_3626, k2_zfmisc_1(B_3627, C_3628)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_3634, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_3631])).
% 4.90/2.02  tff(c_4300, plain, (![A_4736, B_4737, C_4738]: (k4_xboole_0(k2_tarski(A_4736, B_4737), C_4738)=k2_tarski(A_4736, B_4737) | r2_hidden(B_4737, C_4738) | r2_hidden(A_4736, C_4738))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.90/2.02  tff(c_4903, plain, (![D_5130, C_5131, A_5132, B_5133]: (~r2_hidden(D_5130, C_5131) | ~r2_hidden(D_5130, k2_tarski(A_5132, B_5133)) | r2_hidden(B_5133, C_5131) | r2_hidden(A_5132, C_5131))), inference(superposition, [status(thm), theory('equality')], [c_4300, c_4])).
% 4.90/2.02  tff(c_4987, plain, (![C_5187, A_5188, B_5189]: (~r2_hidden(C_5187, k2_tarski(A_5188, B_5189)) | r2_hidden(B_5189, k1_tarski(C_5187)) | r2_hidden(A_5188, k1_tarski(C_5187)))), inference(resolution, [status(thm)], [c_28, c_4903])).
% 4.90/2.02  tff(c_5053, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5'))) | r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_3634, c_4987])).
% 4.90/2.02  tff(c_5058, plain, (r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_5053])).
% 4.90/2.02  tff(c_5075, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_5058, c_26])).
% 4.90/2.02  tff(c_5136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3560, c_5075])).
% 4.90/2.02  tff(c_5137, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_5053])).
% 4.90/2.02  tff(c_5155, plain, (k1_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_5137, c_26])).
% 4.90/2.02  tff(c_5216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3553, c_5155])).
% 4.90/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/2.02  
% 4.90/2.02  Inference rules
% 4.90/2.02  ----------------------
% 4.90/2.02  #Ref     : 0
% 4.90/2.02  #Sup     : 846
% 4.90/2.02  #Fact    : 0
% 4.90/2.02  #Define  : 0
% 4.90/2.02  #Split   : 6
% 4.90/2.02  #Chain   : 0
% 4.90/2.02  #Close   : 0
% 4.90/2.02  
% 4.90/2.02  Ordering : KBO
% 4.90/2.02  
% 4.90/2.02  Simplification rules
% 4.90/2.02  ----------------------
% 4.90/2.02  #Subsume      : 22
% 4.90/2.02  #Demod        : 81
% 4.90/2.02  #Tautology    : 162
% 4.90/2.02  #SimpNegUnit  : 6
% 4.90/2.02  #BackRed      : 4
% 4.90/2.02  
% 4.90/2.02  #Partial instantiations: 3179
% 4.90/2.02  #Strategies tried      : 1
% 4.90/2.02  
% 4.90/2.02  Timing (in seconds)
% 4.90/2.02  ----------------------
% 4.90/2.03  Preprocessing        : 0.32
% 4.90/2.03  Parsing              : 0.16
% 4.90/2.03  CNF conversion       : 0.02
% 4.90/2.03  Main loop            : 0.89
% 4.90/2.03  Inferencing          : 0.41
% 4.90/2.03  Reduction            : 0.20
% 4.90/2.03  Demodulation         : 0.14
% 4.90/2.03  BG Simplification    : 0.05
% 4.90/2.03  Subsumption          : 0.16
% 4.90/2.03  Abstraction          : 0.05
% 4.90/2.03  MUC search           : 0.00
% 4.90/2.03  Cooper               : 0.00
% 4.90/2.03  Total                : 1.24
% 4.90/2.03  Index Insertion      : 0.00
% 4.90/2.03  Index Deletion       : 0.00
% 4.90/2.03  Index Matching       : 0.00
% 4.90/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
