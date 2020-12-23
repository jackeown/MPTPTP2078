%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   82 (  97 expanded)
%              Number of leaves         :   43 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 132 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_96,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_98,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
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

tff(c_74,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_7')
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_154,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_50,plain,(
    ! [A_41] : k3_tarski(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_118,plain,(
    ! [A_64] : r1_tarski(A_64,k1_zfmisc_1(k3_tarski(A_64))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_121,plain,(
    ! [A_41] : r1_tarski(k1_tarski(A_41),k1_zfmisc_1(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_118])).

tff(c_76,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_257,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden(k1_mcart_1(A_109),B_110)
      | ~ r2_hidden(A_109,k2_zfmisc_1(B_110,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_276,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_76,c_257])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_345,plain,(
    ! [B_118] :
      ( r2_hidden(k1_mcart_1('#skF_5'),B_118)
      | ~ r1_tarski(k1_tarski('#skF_6'),B_118) ) ),
    inference(resolution,[status(thm)],[c_276,c_2])).

tff(c_58,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_368,plain,(
    ! [B_119] :
      ( m1_subset_1(k1_mcart_1('#skF_5'),B_119)
      | ~ r1_tarski(k1_tarski('#skF_6'),B_119) ) ),
    inference(resolution,[status(thm)],[c_345,c_58])).

tff(c_381,plain,(
    m1_subset_1(k1_mcart_1('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_121,c_368])).

tff(c_62,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_402,plain,(
    r1_tarski(k1_mcart_1('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_381,c_62])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_404,plain,
    ( k1_mcart_1('#skF_5') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_mcart_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_402,c_14])).

tff(c_407,plain,(
    ~ r1_tarski('#skF_6',k1_mcart_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_404])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),B_31) = k1_tarski(A_30)
      | r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_44] : ~ v1_xboole_0(k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    ! [A_42] : k2_subset_1(A_42) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    ! [A_43] : m1_subset_1(k2_subset_1(A_43),k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77,plain,(
    ! [A_43] : m1_subset_1(A_43,k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_243,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,B_102)
      | ~ r2_hidden(C_103,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_467,plain,(
    ! [C_145,B_146,A_147] :
      ( ~ r2_hidden(C_145,B_146)
      | ~ r2_hidden(C_145,A_147)
      | k4_xboole_0(A_147,B_146) != A_147 ) ),
    inference(resolution,[status(thm)],[c_22,c_243])).

tff(c_5390,plain,(
    ! [A_506,A_507,B_508] :
      ( ~ r2_hidden(A_506,A_507)
      | k4_xboole_0(A_507,B_508) != A_507
      | v1_xboole_0(B_508)
      | ~ m1_subset_1(A_506,B_508) ) ),
    inference(resolution,[status(thm)],[c_60,c_467])).

tff(c_5813,plain,(
    ! [B_525] :
      ( k4_xboole_0(k1_tarski('#skF_6'),B_525) != k1_tarski('#skF_6')
      | v1_xboole_0(B_525)
      | ~ m1_subset_1(k1_mcart_1('#skF_5'),B_525) ) ),
    inference(resolution,[status(thm)],[c_276,c_5390])).

tff(c_5865,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_zfmisc_1(k1_mcart_1('#skF_5'))) != k1_tarski('#skF_6')
    | v1_xboole_0(k1_zfmisc_1(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_77,c_5813])).

tff(c_5895,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_zfmisc_1(k1_mcart_1('#skF_5'))) != k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5865])).

tff(c_6026,plain,(
    r2_hidden('#skF_6',k1_zfmisc_1(k1_mcart_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5895])).

tff(c_6039,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_6026,c_58])).

tff(c_6042,plain,(
    r1_tarski('#skF_6',k1_mcart_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6039,c_62])).

tff(c_6046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_6042])).

tff(c_6047,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6172,plain,(
    ! [A_552,C_553,B_554] :
      ( r2_hidden(k2_mcart_1(A_552),C_553)
      | ~ r2_hidden(A_552,k2_zfmisc_1(B_554,C_553)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6186,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_6172])).

tff(c_6194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6047,c_6186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:22:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.53  
% 6.77/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 6.77/2.53  
% 6.77/2.53  %Foreground sorts:
% 6.77/2.53  
% 6.77/2.53  
% 6.77/2.53  %Background operators:
% 6.77/2.53  
% 6.77/2.53  
% 6.77/2.53  %Foreground operators:
% 6.77/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.77/2.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.77/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.77/2.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.77/2.53  tff('#skF_7', type, '#skF_7': $i).
% 6.77/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.77/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.53  tff('#skF_5', type, '#skF_5': $i).
% 6.77/2.53  tff('#skF_6', type, '#skF_6': $i).
% 6.77/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.77/2.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.77/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.77/2.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.77/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.77/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.77/2.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.77/2.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.77/2.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.77/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.77/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.53  
% 7.05/2.54  tff(f_134, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 7.05/2.54  tff(f_96, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 7.05/2.54  tff(f_88, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.05/2.54  tff(f_123, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.05/2.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.05/2.54  tff(f_107, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.05/2.54  tff(f_117, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.05/2.54  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.05/2.54  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 7.05/2.54  tff(f_103, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.05/2.54  tff(f_98, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.05/2.54  tff(f_100, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.05/2.54  tff(f_113, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.05/2.54  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.05/2.54  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.05/2.54  tff(c_74, plain, (~r2_hidden(k2_mcart_1('#skF_5'), '#skF_7') | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.05/2.54  tff(c_154, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_74])).
% 7.05/2.54  tff(c_50, plain, (![A_41]: (k3_tarski(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.05/2.54  tff(c_118, plain, (![A_64]: (r1_tarski(A_64, k1_zfmisc_1(k3_tarski(A_64))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.05/2.54  tff(c_121, plain, (![A_41]: (r1_tarski(k1_tarski(A_41), k1_zfmisc_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_118])).
% 7.05/2.54  tff(c_76, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.05/2.54  tff(c_257, plain, (![A_109, B_110, C_111]: (r2_hidden(k1_mcart_1(A_109), B_110) | ~r2_hidden(A_109, k2_zfmisc_1(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.05/2.54  tff(c_276, plain, (r2_hidden(k1_mcart_1('#skF_5'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_257])).
% 7.05/2.54  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.05/2.54  tff(c_345, plain, (![B_118]: (r2_hidden(k1_mcart_1('#skF_5'), B_118) | ~r1_tarski(k1_tarski('#skF_6'), B_118))), inference(resolution, [status(thm)], [c_276, c_2])).
% 7.05/2.54  tff(c_58, plain, (![A_45, B_46]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.05/2.54  tff(c_368, plain, (![B_119]: (m1_subset_1(k1_mcart_1('#skF_5'), B_119) | ~r1_tarski(k1_tarski('#skF_6'), B_119))), inference(resolution, [status(thm)], [c_345, c_58])).
% 7.05/2.54  tff(c_381, plain, (m1_subset_1(k1_mcart_1('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_121, c_368])).
% 7.05/2.54  tff(c_62, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.05/2.54  tff(c_402, plain, (r1_tarski(k1_mcart_1('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_381, c_62])).
% 7.05/2.54  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.05/2.54  tff(c_404, plain, (k1_mcart_1('#skF_5')='#skF_6' | ~r1_tarski('#skF_6', k1_mcart_1('#skF_5'))), inference(resolution, [status(thm)], [c_402, c_14])).
% 7.05/2.54  tff(c_407, plain, (~r1_tarski('#skF_6', k1_mcart_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_154, c_404])).
% 7.05/2.54  tff(c_36, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), B_31)=k1_tarski(A_30) | r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.54  tff(c_56, plain, (![A_44]: (~v1_xboole_0(k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.05/2.54  tff(c_52, plain, (![A_42]: (k2_subset_1(A_42)=A_42)), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.05/2.54  tff(c_54, plain, (![A_43]: (m1_subset_1(k2_subset_1(A_43), k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.05/2.54  tff(c_77, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 7.05/2.54  tff(c_60, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | v1_xboole_0(B_48) | ~m1_subset_1(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.05/2.54  tff(c_22, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.05/2.54  tff(c_243, plain, (![A_101, B_102, C_103]: (~r1_xboole_0(A_101, B_102) | ~r2_hidden(C_103, B_102) | ~r2_hidden(C_103, A_101))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.05/2.54  tff(c_467, plain, (![C_145, B_146, A_147]: (~r2_hidden(C_145, B_146) | ~r2_hidden(C_145, A_147) | k4_xboole_0(A_147, B_146)!=A_147)), inference(resolution, [status(thm)], [c_22, c_243])).
% 7.05/2.54  tff(c_5390, plain, (![A_506, A_507, B_508]: (~r2_hidden(A_506, A_507) | k4_xboole_0(A_507, B_508)!=A_507 | v1_xboole_0(B_508) | ~m1_subset_1(A_506, B_508))), inference(resolution, [status(thm)], [c_60, c_467])).
% 7.05/2.54  tff(c_5813, plain, (![B_525]: (k4_xboole_0(k1_tarski('#skF_6'), B_525)!=k1_tarski('#skF_6') | v1_xboole_0(B_525) | ~m1_subset_1(k1_mcart_1('#skF_5'), B_525))), inference(resolution, [status(thm)], [c_276, c_5390])).
% 7.05/2.54  tff(c_5865, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_zfmisc_1(k1_mcart_1('#skF_5')))!=k1_tarski('#skF_6') | v1_xboole_0(k1_zfmisc_1(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_77, c_5813])).
% 7.05/2.54  tff(c_5895, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_zfmisc_1(k1_mcart_1('#skF_5')))!=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_5865])).
% 7.05/2.54  tff(c_6026, plain, (r2_hidden('#skF_6', k1_zfmisc_1(k1_mcart_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5895])).
% 7.05/2.54  tff(c_6039, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_6026, c_58])).
% 7.05/2.54  tff(c_6042, plain, (r1_tarski('#skF_6', k1_mcart_1('#skF_5'))), inference(resolution, [status(thm)], [c_6039, c_62])).
% 7.05/2.54  tff(c_6046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_6042])).
% 7.05/2.54  tff(c_6047, plain, (~r2_hidden(k2_mcart_1('#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 7.05/2.54  tff(c_6172, plain, (![A_552, C_553, B_554]: (r2_hidden(k2_mcart_1(A_552), C_553) | ~r2_hidden(A_552, k2_zfmisc_1(B_554, C_553)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.05/2.54  tff(c_6186, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_76, c_6172])).
% 7.05/2.54  tff(c_6194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6047, c_6186])).
% 7.05/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.54  
% 7.05/2.54  Inference rules
% 7.05/2.54  ----------------------
% 7.05/2.54  #Ref     : 0
% 7.05/2.54  #Sup     : 1402
% 7.05/2.54  #Fact    : 0
% 7.05/2.54  #Define  : 0
% 7.05/2.54  #Split   : 23
% 7.05/2.54  #Chain   : 0
% 7.05/2.54  #Close   : 0
% 7.05/2.54  
% 7.05/2.54  Ordering : KBO
% 7.05/2.54  
% 7.05/2.54  Simplification rules
% 7.05/2.54  ----------------------
% 7.05/2.54  #Subsume      : 124
% 7.05/2.54  #Demod        : 181
% 7.05/2.54  #Tautology    : 203
% 7.05/2.54  #SimpNegUnit  : 57
% 7.05/2.54  #BackRed      : 1
% 7.05/2.54  
% 7.05/2.54  #Partial instantiations: 0
% 7.05/2.54  #Strategies tried      : 1
% 7.05/2.54  
% 7.05/2.54  Timing (in seconds)
% 7.05/2.54  ----------------------
% 7.05/2.55  Preprocessing        : 0.35
% 7.05/2.55  Parsing              : 0.18
% 7.05/2.55  CNF conversion       : 0.02
% 7.05/2.55  Main loop            : 1.44
% 7.05/2.55  Inferencing          : 0.47
% 7.05/2.55  Reduction            : 0.44
% 7.05/2.55  Demodulation         : 0.29
% 7.05/2.55  BG Simplification    : 0.05
% 7.05/2.55  Subsumption          : 0.35
% 7.05/2.55  Abstraction          : 0.06
% 7.05/2.55  MUC search           : 0.00
% 7.05/2.55  Cooper               : 0.00
% 7.05/2.55  Total                : 1.81
% 7.05/2.55  Index Insertion      : 0.00
% 7.05/2.55  Index Deletion       : 0.00
% 7.05/2.55  Index Matching       : 0.00
% 7.05/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
