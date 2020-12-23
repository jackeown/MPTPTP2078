%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 200 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 376 expanded)
%              Number of equality atoms :   49 ( 202 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
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

tff(c_38,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1498,plain,(
    ! [A_7176,B_7177] : k1_enumset1(A_7176,A_7176,B_7177) = k2_tarski(A_7176,B_7177) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1516,plain,(
    ! [A_7178,B_7179] : r2_hidden(A_7178,k2_tarski(A_7178,B_7179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_20])).

tff(c_1519,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1516])).

tff(c_79,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [B_47,A_48] : r2_hidden(B_47,k2_tarski(A_48,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_100,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_97])).

tff(c_50,plain,
    ( '#skF_5' != '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_55,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_74,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(k1_tarski(A_43),B_44)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(k1_tarski(A_64),B_65) = k1_tarski(A_64)
      | r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_74,c_10])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_148,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_119])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_121,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,B_59)
      | ~ r2_hidden(C_60,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_450,plain,(
    ! [C_121,B_122,A_123] :
      ( ~ r2_hidden(C_121,B_122)
      | ~ r2_hidden(C_121,k1_tarski(A_123))
      | r2_hidden(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_46,c_121])).

tff(c_512,plain,(
    ! [E_136,A_137,B_138,C_139] :
      ( ~ r2_hidden(E_136,k1_tarski(A_137))
      | r2_hidden(A_137,k1_enumset1(E_136,B_138,C_139)) ) ),
    inference(resolution,[status(thm)],[c_20,c_450])).

tff(c_531,plain,(
    ! [B_140,C_141] : r2_hidden('#skF_5',k1_enumset1('#skF_4',B_140,C_141)) ),
    inference(resolution,[status(thm)],[c_148,c_512])).

tff(c_14,plain,(
    ! [E_16,C_12,B_11,A_10] :
      ( E_16 = C_12
      | E_16 = B_11
      | E_16 = A_10
      | ~ r2_hidden(E_16,k1_enumset1(A_10,B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_536,plain,(
    ! [C_141,B_140] :
      ( C_141 = '#skF_5'
      | B_140 = '#skF_5'
      | '#skF_5' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_531,c_14])).

tff(c_546,plain,(
    ! [C_141,B_140] :
      ( C_141 = '#skF_5'
      | B_140 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_536])).

tff(c_551,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_549,plain,(
    ! [B_140] : B_140 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_750,plain,(
    ! [B_1892] : B_1892 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_549])).

tff(c_922,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_55])).

tff(c_925,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_923,plain,(
    ! [C_141] : C_141 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_1124,plain,(
    ! [C_5366] : C_5366 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_923])).

tff(c_1296,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_55])).

tff(c_1297,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1298,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1341,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1298,c_52])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1316,plain,(
    ! [A_7137,B_7138,C_7139] :
      ( ~ r1_xboole_0(A_7137,B_7138)
      | ~ r2_hidden(C_7139,B_7138)
      | ~ r2_hidden(C_7139,A_7137) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1420,plain,(
    ! [C_7153,B_7154,A_7155] :
      ( ~ r2_hidden(C_7153,B_7154)
      | ~ r2_hidden(C_7153,A_7155)
      | k4_xboole_0(A_7155,B_7154) != A_7155 ) ),
    inference(resolution,[status(thm)],[c_12,c_1316])).

tff(c_1454,plain,(
    ! [A_7160,A_7161] :
      ( ~ r2_hidden(A_7160,A_7161)
      | k4_xboole_0(A_7161,k1_tarski(A_7160)) != A_7161 ) ),
    inference(resolution,[status(thm)],[c_100,c_1420])).

tff(c_1457,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1341,c_1454])).

tff(c_1468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1457])).

tff(c_1469,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1470,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( '#skF_5' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1522,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1470,c_54])).

tff(c_1558,plain,(
    ! [A_7194,B_7195,C_7196] :
      ( ~ r1_xboole_0(A_7194,B_7195)
      | ~ r2_hidden(C_7196,B_7195)
      | ~ r2_hidden(C_7196,A_7194) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1585,plain,(
    ! [C_7199,B_7200,A_7201] :
      ( ~ r2_hidden(C_7199,B_7200)
      | ~ r2_hidden(C_7199,A_7201)
      | k4_xboole_0(A_7201,B_7200) != A_7201 ) ),
    inference(resolution,[status(thm)],[c_12,c_1558])).

tff(c_1610,plain,(
    ! [A_7202,A_7203] :
      ( ~ r2_hidden(A_7202,A_7203)
      | k4_xboole_0(A_7203,k1_tarski(A_7202)) != A_7203 ) ),
    inference(resolution,[status(thm)],[c_1519,c_1585])).

tff(c_1617,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_1610])).

tff(c_1622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_1617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:05:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.63  
% 3.44/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.63  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.44/1.63  
% 3.44/1.63  %Foreground sorts:
% 3.44/1.63  
% 3.44/1.63  
% 3.44/1.63  %Background operators:
% 3.44/1.63  
% 3.44/1.63  
% 3.44/1.63  %Foreground operators:
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.44/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.44/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.44/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.63  
% 3.85/1.65  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.65  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.85/1.65  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.85/1.65  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.85/1.65  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.85/1.65  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.85/1.65  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.85/1.65  tff(c_38, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.85/1.65  tff(c_1498, plain, (![A_7176, B_7177]: (k1_enumset1(A_7176, A_7176, B_7177)=k2_tarski(A_7176, B_7177))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.65  tff(c_20, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.65  tff(c_1516, plain, (![A_7178, B_7179]: (r2_hidden(A_7178, k2_tarski(A_7178, B_7179)))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_20])).
% 3.85/1.65  tff(c_1519, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1516])).
% 3.85/1.65  tff(c_79, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.65  tff(c_16, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.65  tff(c_97, plain, (![B_47, A_48]: (r2_hidden(B_47, k2_tarski(A_48, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 3.85/1.65  tff(c_100, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_97])).
% 3.85/1.65  tff(c_50, plain, ('#skF_5'!='#skF_4' | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.85/1.65  tff(c_55, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 3.85/1.65  tff(c_74, plain, (![A_43, B_44]: (r1_xboole_0(k1_tarski(A_43), B_44) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.65  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.85/1.65  tff(c_137, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), B_65)=k1_tarski(A_64) | r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_74, c_10])).
% 3.85/1.65  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.85/1.65  tff(c_119, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 3.85/1.65  tff(c_148, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_119])).
% 3.85/1.65  tff(c_46, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.65  tff(c_121, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, B_59) | ~r2_hidden(C_60, A_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.65  tff(c_450, plain, (![C_121, B_122, A_123]: (~r2_hidden(C_121, B_122) | ~r2_hidden(C_121, k1_tarski(A_123)) | r2_hidden(A_123, B_122))), inference(resolution, [status(thm)], [c_46, c_121])).
% 3.85/1.65  tff(c_512, plain, (![E_136, A_137, B_138, C_139]: (~r2_hidden(E_136, k1_tarski(A_137)) | r2_hidden(A_137, k1_enumset1(E_136, B_138, C_139)))), inference(resolution, [status(thm)], [c_20, c_450])).
% 3.85/1.65  tff(c_531, plain, (![B_140, C_141]: (r2_hidden('#skF_5', k1_enumset1('#skF_4', B_140, C_141)))), inference(resolution, [status(thm)], [c_148, c_512])).
% 3.85/1.65  tff(c_14, plain, (![E_16, C_12, B_11, A_10]: (E_16=C_12 | E_16=B_11 | E_16=A_10 | ~r2_hidden(E_16, k1_enumset1(A_10, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.65  tff(c_536, plain, (![C_141, B_140]: (C_141='#skF_5' | B_140='#skF_5' | '#skF_5'='#skF_4')), inference(resolution, [status(thm)], [c_531, c_14])).
% 3.85/1.65  tff(c_546, plain, (![C_141, B_140]: (C_141='#skF_5' | B_140='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_55, c_536])).
% 3.85/1.65  tff(c_551, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_546])).
% 3.85/1.65  tff(c_549, plain, (![B_140]: (B_140='#skF_5')), inference(splitLeft, [status(thm)], [c_546])).
% 3.85/1.65  tff(c_750, plain, (![B_1892]: (B_1892='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_551, c_549])).
% 3.85/1.65  tff(c_922, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_750, c_55])).
% 3.85/1.65  tff(c_925, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_546])).
% 3.85/1.65  tff(c_923, plain, (![C_141]: (C_141='#skF_5')), inference(splitRight, [status(thm)], [c_546])).
% 3.85/1.65  tff(c_1124, plain, (![C_5366]: (C_5366='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_925, c_923])).
% 3.85/1.65  tff(c_1296, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1124, c_55])).
% 3.85/1.65  tff(c_1297, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 3.85/1.65  tff(c_1298, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.85/1.65  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.85/1.65  tff(c_1341, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1298, c_52])).
% 3.85/1.65  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.85/1.65  tff(c_1316, plain, (![A_7137, B_7138, C_7139]: (~r1_xboole_0(A_7137, B_7138) | ~r2_hidden(C_7139, B_7138) | ~r2_hidden(C_7139, A_7137))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.65  tff(c_1420, plain, (![C_7153, B_7154, A_7155]: (~r2_hidden(C_7153, B_7154) | ~r2_hidden(C_7153, A_7155) | k4_xboole_0(A_7155, B_7154)!=A_7155)), inference(resolution, [status(thm)], [c_12, c_1316])).
% 3.85/1.65  tff(c_1454, plain, (![A_7160, A_7161]: (~r2_hidden(A_7160, A_7161) | k4_xboole_0(A_7161, k1_tarski(A_7160))!=A_7161)), inference(resolution, [status(thm)], [c_100, c_1420])).
% 3.85/1.65  tff(c_1457, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1341, c_1454])).
% 3.85/1.65  tff(c_1468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_1457])).
% 3.85/1.65  tff(c_1469, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 3.85/1.65  tff(c_1470, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 3.85/1.65  tff(c_54, plain, ('#skF_5'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.85/1.65  tff(c_1522, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1470, c_54])).
% 3.85/1.65  tff(c_1558, plain, (![A_7194, B_7195, C_7196]: (~r1_xboole_0(A_7194, B_7195) | ~r2_hidden(C_7196, B_7195) | ~r2_hidden(C_7196, A_7194))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.65  tff(c_1585, plain, (![C_7199, B_7200, A_7201]: (~r2_hidden(C_7199, B_7200) | ~r2_hidden(C_7199, A_7201) | k4_xboole_0(A_7201, B_7200)!=A_7201)), inference(resolution, [status(thm)], [c_12, c_1558])).
% 3.85/1.65  tff(c_1610, plain, (![A_7202, A_7203]: (~r2_hidden(A_7202, A_7203) | k4_xboole_0(A_7203, k1_tarski(A_7202))!=A_7203)), inference(resolution, [status(thm)], [c_1519, c_1585])).
% 3.85/1.65  tff(c_1617, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_1610])).
% 3.85/1.65  tff(c_1622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1519, c_1617])).
% 3.85/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.65  
% 3.85/1.65  Inference rules
% 3.85/1.65  ----------------------
% 3.85/1.65  #Ref     : 0
% 3.85/1.65  #Sup     : 544
% 3.85/1.65  #Fact    : 0
% 3.85/1.65  #Define  : 0
% 3.85/1.65  #Split   : 4
% 3.85/1.65  #Chain   : 0
% 3.85/1.65  #Close   : 0
% 3.85/1.65  
% 3.85/1.65  Ordering : KBO
% 3.85/1.65  
% 3.85/1.65  Simplification rules
% 3.85/1.65  ----------------------
% 3.85/1.65  #Subsume      : 57
% 3.85/1.65  #Demod        : 72
% 3.85/1.65  #Tautology    : 110
% 3.85/1.65  #SimpNegUnit  : 1
% 3.85/1.65  #BackRed      : 0
% 3.85/1.65  
% 3.85/1.65  #Partial instantiations: 224
% 3.85/1.65  #Strategies tried      : 1
% 3.85/1.65  
% 3.85/1.65  Timing (in seconds)
% 3.85/1.65  ----------------------
% 3.85/1.65  Preprocessing        : 0.33
% 3.85/1.65  Parsing              : 0.16
% 3.85/1.65  CNF conversion       : 0.02
% 3.85/1.65  Main loop            : 0.55
% 3.85/1.65  Inferencing          : 0.24
% 3.85/1.65  Reduction            : 0.15
% 3.85/1.65  Demodulation         : 0.11
% 3.85/1.65  BG Simplification    : 0.03
% 3.85/1.65  Subsumption          : 0.09
% 3.85/1.65  Abstraction          : 0.03
% 3.85/1.65  MUC search           : 0.00
% 3.85/1.65  Cooper               : 0.00
% 3.85/1.65  Total                : 0.91
% 3.85/1.65  Index Insertion      : 0.00
% 3.85/1.65  Index Deletion       : 0.00
% 3.85/1.65  Index Matching       : 0.00
% 3.85/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
