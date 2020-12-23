%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 149 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 282 expanded)
%              Number of equality atoms :   21 (  53 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ! [D] :
                ( m1_subset_1(D,A)
               => ( A != k1_xboole_0
                 => m1_subset_1(k1_enumset1(B,C,D),k1_zfmisc_1(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_68,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_446,plain,(
    ! [B_100,A_101] :
      ( m1_subset_1(k1_tarski(B_100),k1_zfmisc_1(A_101))
      | k1_xboole_0 = A_101
      | ~ m1_subset_1(B_100,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_411,plain,(
    ! [C_92,A_93,B_94] :
      ( r2_hidden(C_92,A_93)
      | ~ r2_hidden(C_92,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_420,plain,(
    ! [C_12,A_93] :
      ( r2_hidden(C_12,A_93)
      | ~ m1_subset_1(k1_tarski(C_12),k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_10,c_411])).

tff(c_456,plain,(
    ! [B_100,A_101] :
      ( r2_hidden(B_100,A_101)
      | k1_xboole_0 = A_101
      | ~ m1_subset_1(B_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_446,c_420])).

tff(c_70,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(k2_tarski(A_29,B_30),C_31)
      | ~ r2_hidden(B_30,C_31)
      | ~ r2_hidden(A_29,C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_290,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_297,plain,(
    ! [B_83,A_22] :
      ( r1_tarski(B_83,A_22)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_290,c_26])).

tff(c_308,plain,(
    ! [B_83,A_22] :
      ( r1_tarski(B_83,A_22)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_22)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_297])).

tff(c_457,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(k1_tarski(B_100),A_101)
      | k1_xboole_0 = A_101
      | ~ m1_subset_1(B_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_446,c_308])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1197,plain,(
    ! [A_218,C_219,B_220] :
      ( r1_tarski(k2_xboole_0(A_218,C_219),B_220)
      | ~ r1_tarski(C_219,B_220)
      | ~ r1_tarski(A_218,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1882,plain,(
    ! [A_337,B_338,C_339,B_340] :
      ( r1_tarski(k1_enumset1(A_337,B_338,C_339),B_340)
      | ~ r1_tarski(k2_tarski(B_338,C_339),B_340)
      | ~ r1_tarski(k1_tarski(A_337),B_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1197])).

tff(c_28,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_206,plain,(
    ! [B_75,A_76] :
      ( m1_subset_1(B_75,A_76)
      | ~ r2_hidden(B_75,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_209,plain,(
    ! [C_26,A_22] :
      ( m1_subset_1(C_26,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(resolution,[status(thm)],[c_28,c_206])).

tff(c_281,plain,(
    ! [C_81,A_82] :
      ( m1_subset_1(C_81,k1_zfmisc_1(A_82))
      | ~ r1_tarski(C_81,A_82) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_209])).

tff(c_24,plain,(
    ! [B_20,A_19,C_21] : k1_enumset1(B_20,A_19,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_16,C_18,B_17] : k1_enumset1(A_16,C_18,B_17) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ~ m1_subset_1(k1_enumset1('#skF_6','#skF_7','#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_71,plain,(
    ~ m1_subset_1(k1_enumset1('#skF_6','#skF_8','#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_72,plain,(
    ~ m1_subset_1(k1_enumset1('#skF_8','#skF_6','#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_71])).

tff(c_289,plain,(
    ~ r1_tarski(k1_enumset1('#skF_8','#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_281,c_72])).

tff(c_1913,plain,
    ( ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1882,c_289])).

tff(c_1914,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1913])).

tff(c_1917,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_457,c_1914])).

tff(c_1923,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1917])).

tff(c_1925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1923])).

tff(c_1926,plain,(
    ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1913])).

tff(c_1955,plain,
    ( ~ r2_hidden('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1926])).

tff(c_1957,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_1963,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_456,c_1957])).

tff(c_1970,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1963])).

tff(c_1972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1970])).

tff(c_1973,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_1980,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_456,c_1973])).

tff(c_1987,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1980])).

tff(c_1989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.74  
% 4.14/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.74  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.14/1.74  
% 4.14/1.74  %Foreground sorts:
% 4.14/1.74  
% 4.14/1.74  
% 4.14/1.74  %Background operators:
% 4.14/1.74  
% 4.14/1.74  
% 4.14/1.74  %Foreground operators:
% 4.14/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.14/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.14/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.14/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.14/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.14/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.74  tff('#skF_8', type, '#skF_8': $i).
% 4.14/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.14/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.14/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.14/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.14/1.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.14/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.74  
% 4.14/1.76  tff(f_112, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_enumset1(B, C, D), k1_zfmisc_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_subset_1)).
% 4.14/1.76  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 4.14/1.76  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.14/1.76  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.14/1.76  tff(f_68, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.14/1.76  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.14/1.76  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.14/1.76  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.14/1.76  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 4.14/1.76  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.14/1.76  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 4.14/1.76  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 4.14/1.76  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.14/1.76  tff(c_68, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.14/1.76  tff(c_446, plain, (![B_100, A_101]: (m1_subset_1(k1_tarski(B_100), k1_zfmisc_1(A_101)) | k1_xboole_0=A_101 | ~m1_subset_1(B_100, A_101))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.14/1.76  tff(c_10, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.14/1.76  tff(c_411, plain, (![C_92, A_93, B_94]: (r2_hidden(C_92, A_93) | ~r2_hidden(C_92, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.14/1.76  tff(c_420, plain, (![C_12, A_93]: (r2_hidden(C_12, A_93) | ~m1_subset_1(k1_tarski(C_12), k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_10, c_411])).
% 4.14/1.76  tff(c_456, plain, (![B_100, A_101]: (r2_hidden(B_100, A_101) | k1_xboole_0=A_101 | ~m1_subset_1(B_100, A_101))), inference(resolution, [status(thm)], [c_446, c_420])).
% 4.14/1.76  tff(c_70, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.14/1.76  tff(c_42, plain, (![A_29, B_30, C_31]: (r1_tarski(k2_tarski(A_29, B_30), C_31) | ~r2_hidden(B_30, C_31) | ~r2_hidden(A_29, C_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.14/1.76  tff(c_66, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.14/1.76  tff(c_56, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.14/1.76  tff(c_290, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.14/1.76  tff(c_26, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.14/1.76  tff(c_297, plain, (![B_83, A_22]: (r1_tarski(B_83, A_22) | ~m1_subset_1(B_83, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_290, c_26])).
% 4.14/1.76  tff(c_308, plain, (![B_83, A_22]: (r1_tarski(B_83, A_22) | ~m1_subset_1(B_83, k1_zfmisc_1(A_22)))), inference(negUnitSimplification, [status(thm)], [c_56, c_297])).
% 4.14/1.76  tff(c_457, plain, (![B_100, A_101]: (r1_tarski(k1_tarski(B_100), A_101) | k1_xboole_0=A_101 | ~m1_subset_1(B_100, A_101))), inference(resolution, [status(thm)], [c_446, c_308])).
% 4.14/1.76  tff(c_20, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.14/1.76  tff(c_1197, plain, (![A_218, C_219, B_220]: (r1_tarski(k2_xboole_0(A_218, C_219), B_220) | ~r1_tarski(C_219, B_220) | ~r1_tarski(A_218, B_220))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.14/1.76  tff(c_1882, plain, (![A_337, B_338, C_339, B_340]: (r1_tarski(k1_enumset1(A_337, B_338, C_339), B_340) | ~r1_tarski(k2_tarski(B_338, C_339), B_340) | ~r1_tarski(k1_tarski(A_337), B_340))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1197])).
% 4.14/1.76  tff(c_28, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.14/1.76  tff(c_206, plain, (![B_75, A_76]: (m1_subset_1(B_75, A_76) | ~r2_hidden(B_75, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.14/1.76  tff(c_209, plain, (![C_26, A_22]: (m1_subset_1(C_26, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(resolution, [status(thm)], [c_28, c_206])).
% 4.14/1.76  tff(c_281, plain, (![C_81, A_82]: (m1_subset_1(C_81, k1_zfmisc_1(A_82)) | ~r1_tarski(C_81, A_82))), inference(negUnitSimplification, [status(thm)], [c_56, c_209])).
% 4.14/1.76  tff(c_24, plain, (![B_20, A_19, C_21]: (k1_enumset1(B_20, A_19, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.14/1.76  tff(c_22, plain, (![A_16, C_18, B_17]: (k1_enumset1(A_16, C_18, B_17)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.76  tff(c_62, plain, (~m1_subset_1(k1_enumset1('#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.14/1.76  tff(c_71, plain, (~m1_subset_1(k1_enumset1('#skF_6', '#skF_8', '#skF_7'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62])).
% 4.14/1.76  tff(c_72, plain, (~m1_subset_1(k1_enumset1('#skF_8', '#skF_6', '#skF_7'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_71])).
% 4.14/1.76  tff(c_289, plain, (~r1_tarski(k1_enumset1('#skF_8', '#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_281, c_72])).
% 4.14/1.76  tff(c_1913, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_1882, c_289])).
% 4.14/1.76  tff(c_1914, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1913])).
% 4.14/1.76  tff(c_1917, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_457, c_1914])).
% 4.14/1.76  tff(c_1923, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1917])).
% 4.14/1.76  tff(c_1925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1923])).
% 4.14/1.76  tff(c_1926, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_1913])).
% 4.14/1.76  tff(c_1955, plain, (~r2_hidden('#skF_7', '#skF_5') | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1926])).
% 4.14/1.76  tff(c_1957, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1955])).
% 4.14/1.76  tff(c_1963, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_456, c_1957])).
% 4.14/1.76  tff(c_1970, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1963])).
% 4.14/1.76  tff(c_1972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1970])).
% 4.14/1.76  tff(c_1973, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_1955])).
% 4.14/1.76  tff(c_1980, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_456, c_1973])).
% 4.14/1.76  tff(c_1987, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1980])).
% 4.14/1.76  tff(c_1989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1987])).
% 4.14/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.76  
% 4.14/1.76  Inference rules
% 4.14/1.76  ----------------------
% 4.14/1.76  #Ref     : 0
% 4.14/1.76  #Sup     : 429
% 4.14/1.76  #Fact    : 0
% 4.14/1.76  #Define  : 0
% 4.14/1.76  #Split   : 6
% 4.14/1.76  #Chain   : 0
% 4.14/1.76  #Close   : 0
% 4.14/1.76  
% 4.14/1.76  Ordering : KBO
% 4.14/1.76  
% 4.14/1.76  Simplification rules
% 4.14/1.76  ----------------------
% 4.14/1.76  #Subsume      : 134
% 4.14/1.76  #Demod        : 24
% 4.14/1.76  #Tautology    : 80
% 4.14/1.76  #SimpNegUnit  : 48
% 4.14/1.76  #BackRed      : 2
% 4.14/1.76  
% 4.14/1.76  #Partial instantiations: 0
% 4.14/1.76  #Strategies tried      : 1
% 4.14/1.76  
% 4.14/1.76  Timing (in seconds)
% 4.14/1.76  ----------------------
% 4.14/1.76  Preprocessing        : 0.34
% 4.14/1.76  Parsing              : 0.18
% 4.14/1.76  CNF conversion       : 0.03
% 4.14/1.76  Main loop            : 0.66
% 4.14/1.76  Inferencing          : 0.23
% 4.14/1.76  Reduction            : 0.21
% 4.14/1.76  Demodulation         : 0.15
% 4.14/1.76  BG Simplification    : 0.03
% 4.14/1.76  Subsumption          : 0.14
% 4.14/1.76  Abstraction          : 0.03
% 4.14/1.76  MUC search           : 0.00
% 4.14/1.76  Cooper               : 0.00
% 4.14/1.76  Total                : 1.03
% 4.14/1.76  Index Insertion      : 0.00
% 4.14/1.76  Index Deletion       : 0.00
% 4.14/1.76  Index Matching       : 0.00
% 4.14/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
