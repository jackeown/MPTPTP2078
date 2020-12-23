%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 152 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 261 expanded)
%              Number of equality atoms :   28 (  91 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_62,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_10' != '#skF_12'
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( '#skF_6' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_123,plain,(
    ! [A_53,C_54,B_55,D_56] :
      ( r2_hidden(A_53,C_54)
      | ~ r2_hidden(k4_tarski(A_53,B_55),k2_zfmisc_1(C_54,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_117,c_123])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_126])).

tff(c_132,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_70,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_173,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_70])).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    ! [B_38,A_39] : r2_hidden(B_38,k2_tarski(A_39,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_22])).

tff(c_106,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_48,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_247,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_66])).

tff(c_248,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_247])).

tff(c_251,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_248])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_106,c_251])).

tff(c_257,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_256,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_258,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_292,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_300,plain,(
    ! [B_106,D_107,A_108,C_109] :
      ( r2_hidden(B_106,D_107)
      | ~ r2_hidden(k4_tarski(A_108,B_106),k2_zfmisc_1(C_109,D_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_304,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_292,c_300])).

tff(c_320,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden(A_113,k4_xboole_0(B_114,k1_tarski(C_115)))
      | C_115 = A_113
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_354,plain,(
    ! [A_120,C_121,B_122] :
      ( ~ r2_hidden(A_120,k1_tarski(C_121))
      | C_121 = A_120
      | ~ r2_hidden(A_120,B_122) ) ),
    inference(resolution,[status(thm)],[c_320,c_4])).

tff(c_356,plain,(
    ! [B_122] :
      ( '#skF_10' = '#skF_12'
      | ~ r2_hidden('#skF_10',B_122) ) ),
    inference(resolution,[status(thm)],[c_304,c_354])).

tff(c_361,plain,(
    ! [B_122] : ~ r2_hidden('#skF_10',B_122) ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_356])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_304])).

tff(c_367,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_372,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_372])).

tff(c_374,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_261,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_279,plain,(
    ! [B_91,A_92] : r2_hidden(B_91,k2_tarski(A_92,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_22])).

tff(c_282,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_279])).

tff(c_366,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_574,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_66])).

tff(c_575,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_574])).

tff(c_578,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_282,c_578])).

tff(c_584,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_64,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | '#skF_10' != '#skF_12'
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_624,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_584,c_64])).

tff(c_593,plain,(
    ! [A_161,B_162] : k1_enumset1(A_161,A_161,B_162) = k2_tarski(A_161,B_162) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_611,plain,(
    ! [B_163,A_164] : r2_hidden(B_163,k2_tarski(A_164,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_22])).

tff(c_614,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_611])).

tff(c_706,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( r2_hidden(k4_tarski(A_200,B_201),k2_zfmisc_1(C_202,D_203))
      | ~ r2_hidden(B_201,D_203)
      | ~ r2_hidden(A_200,C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_583,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_60,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | '#skF_10' != '#skF_12'
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_699,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_584,c_583,c_60])).

tff(c_709,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_706,c_699])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_614,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:49:51 EST 2020
% 0.18/0.32  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.43  
% 2.32/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.43  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_12
% 2.32/1.43  
% 2.32/1.43  %Foreground sorts:
% 2.32/1.43  
% 2.32/1.43  
% 2.32/1.43  %Background operators:
% 2.32/1.43  
% 2.32/1.43  
% 2.32/1.43  %Foreground operators:
% 2.32/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.32/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.43  tff('#skF_11', type, '#skF_11': $i).
% 2.32/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.32/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.32/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.32/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.32/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.32/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.32/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.32/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.32/1.43  tff('#skF_12', type, '#skF_12': $i).
% 2.32/1.43  
% 2.32/1.44  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.32/1.44  tff(f_60, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.32/1.44  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.32/1.44  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.32/1.44  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.32/1.44  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.32/1.44  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.32/1.44  tff(c_62, plain, ('#skF_6'='#skF_8' | '#skF_10'!='#skF_12' | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.44  tff(c_84, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_62])).
% 2.32/1.44  tff(c_68, plain, ('#skF_6'='#skF_8' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.44  tff(c_117, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_68])).
% 2.32/1.44  tff(c_123, plain, (![A_53, C_54, B_55, D_56]: (r2_hidden(A_53, C_54) | ~r2_hidden(k4_tarski(A_53, B_55), k2_zfmisc_1(C_54, D_56)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.44  tff(c_126, plain, (r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_117, c_123])).
% 2.32/1.44  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_126])).
% 2.32/1.44  tff(c_132, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_68])).
% 2.32/1.44  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.44  tff(c_173, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_132, c_70])).
% 2.32/1.44  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.44  tff(c_85, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.44  tff(c_22, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.44  tff(c_103, plain, (![B_38, A_39]: (r2_hidden(B_38, k2_tarski(A_39, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_22])).
% 2.32/1.44  tff(c_106, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_103])).
% 2.32/1.44  tff(c_48, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.44  tff(c_131, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_68])).
% 2.32/1.44  tff(c_66, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.44  tff(c_247, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_66])).
% 2.32/1.44  tff(c_248, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_132, c_247])).
% 2.32/1.44  tff(c_251, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_248])).
% 2.32/1.44  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_106, c_251])).
% 2.32/1.44  tff(c_257, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_62])).
% 2.32/1.44  tff(c_256, plain, ('#skF_10'!='#skF_12' | '#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_62])).
% 2.32/1.44  tff(c_258, plain, ('#skF_10'!='#skF_12'), inference(splitLeft, [status(thm)], [c_256])).
% 2.32/1.44  tff(c_292, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_68])).
% 2.32/1.44  tff(c_300, plain, (![B_106, D_107, A_108, C_109]: (r2_hidden(B_106, D_107) | ~r2_hidden(k4_tarski(A_108, B_106), k2_zfmisc_1(C_109, D_107)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.44  tff(c_304, plain, (r2_hidden('#skF_10', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_292, c_300])).
% 2.32/1.44  tff(c_320, plain, (![A_113, B_114, C_115]: (r2_hidden(A_113, k4_xboole_0(B_114, k1_tarski(C_115))) | C_115=A_113 | ~r2_hidden(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.32/1.44  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.44  tff(c_354, plain, (![A_120, C_121, B_122]: (~r2_hidden(A_120, k1_tarski(C_121)) | C_121=A_120 | ~r2_hidden(A_120, B_122))), inference(resolution, [status(thm)], [c_320, c_4])).
% 2.32/1.44  tff(c_356, plain, (![B_122]: ('#skF_10'='#skF_12' | ~r2_hidden('#skF_10', B_122))), inference(resolution, [status(thm)], [c_304, c_354])).
% 2.32/1.44  tff(c_361, plain, (![B_122]: (~r2_hidden('#skF_10', B_122))), inference(negUnitSimplification, [status(thm)], [c_258, c_356])).
% 2.32/1.44  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_304])).
% 2.32/1.44  tff(c_367, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_68])).
% 2.32/1.44  tff(c_372, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_70])).
% 2.32/1.44  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_372])).
% 2.32/1.44  tff(c_374, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 2.32/1.44  tff(c_261, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.44  tff(c_279, plain, (![B_91, A_92]: (r2_hidden(B_91, k2_tarski(A_92, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_22])).
% 2.32/1.44  tff(c_282, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_279])).
% 2.32/1.44  tff(c_366, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_68])).
% 2.32/1.44  tff(c_574, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_66])).
% 2.32/1.44  tff(c_575, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_367, c_574])).
% 2.32/1.44  tff(c_578, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_575])).
% 2.32/1.44  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_282, c_578])).
% 2.32/1.44  tff(c_584, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_256])).
% 2.32/1.44  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_7') | '#skF_10'!='#skF_12' | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.44  tff(c_624, plain, (r2_hidden('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_584, c_64])).
% 2.32/1.44  tff(c_593, plain, (![A_161, B_162]: (k1_enumset1(A_161, A_161, B_162)=k2_tarski(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.44  tff(c_611, plain, (![B_163, A_164]: (r2_hidden(B_163, k2_tarski(A_164, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_593, c_22])).
% 2.32/1.44  tff(c_614, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_611])).
% 2.32/1.44  tff(c_706, plain, (![A_200, B_201, C_202, D_203]: (r2_hidden(k4_tarski(A_200, B_201), k2_zfmisc_1(C_202, D_203)) | ~r2_hidden(B_201, D_203) | ~r2_hidden(A_200, C_202))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.44  tff(c_583, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_256])).
% 2.32/1.44  tff(c_60, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))) | '#skF_10'!='#skF_12' | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.44  tff(c_699, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_584, c_583, c_60])).
% 2.32/1.44  tff(c_709, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_706, c_699])).
% 2.32/1.44  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_624, c_614, c_709])).
% 2.32/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.44  
% 2.32/1.44  Inference rules
% 2.32/1.44  ----------------------
% 2.32/1.44  #Ref     : 0
% 2.32/1.44  #Sup     : 128
% 2.32/1.44  #Fact    : 0
% 2.32/1.44  #Define  : 0
% 2.32/1.44  #Split   : 5
% 2.32/1.44  #Chain   : 0
% 2.32/1.44  #Close   : 0
% 2.32/1.44  
% 2.32/1.44  Ordering : KBO
% 2.32/1.44  
% 2.32/1.44  Simplification rules
% 2.32/1.44  ----------------------
% 2.32/1.44  #Subsume      : 7
% 2.32/1.44  #Demod        : 35
% 2.32/1.44  #Tautology    : 76
% 2.32/1.44  #SimpNegUnit  : 7
% 2.32/1.44  #BackRed      : 1
% 2.32/1.44  
% 2.32/1.44  #Partial instantiations: 0
% 2.32/1.44  #Strategies tried      : 1
% 2.32/1.44  
% 2.32/1.44  Timing (in seconds)
% 2.32/1.44  ----------------------
% 2.32/1.45  Preprocessing        : 0.28
% 2.32/1.45  Parsing              : 0.13
% 2.32/1.45  CNF conversion       : 0.03
% 2.32/1.45  Main loop            : 0.32
% 2.32/1.45  Inferencing          : 0.12
% 2.32/1.45  Reduction            : 0.09
% 2.32/1.45  Demodulation         : 0.07
% 2.32/1.45  BG Simplification    : 0.02
% 2.32/1.45  Subsumption          : 0.06
% 2.32/1.45  Abstraction          : 0.02
% 2.32/1.45  MUC search           : 0.00
% 2.32/1.45  Cooper               : 0.00
% 2.32/1.45  Total                : 0.64
% 2.32/1.45  Index Insertion      : 0.00
% 2.32/1.45  Index Deletion       : 0.00
% 2.32/1.45  Index Matching       : 0.00
% 2.32/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
