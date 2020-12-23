%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 260 expanded)
%              Number of equality atoms :   17 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_44,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_7' != '#skF_9'
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_185,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r2_hidden(A_67,C_68)
      | ~ r2_hidden(k4_tarski(A_67,B_69),k2_zfmisc_1(C_68,D_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_188,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_148,c_185])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_188])).

tff(c_194,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_212,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_52])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | ~ r1_tarski(k1_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( r2_hidden(k4_tarski(A_16,B_17),k2_zfmisc_1(C_18,D_19))
      | ~ r2_hidden(B_17,D_19)
      | ~ r2_hidden(A_16,C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_193,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_452,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3')))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_48])).

tff(c_453,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_452])).

tff(c_456,plain,
    ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_453])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_75,c_456])).

tff(c_462,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_657,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_499,plain,(
    ! [B_130,C_131,A_132] :
      ( r2_hidden(B_130,C_131)
      | ~ r1_tarski(k2_tarski(A_132,B_130),C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_507,plain,(
    ! [B_130,A_132] : r2_hidden(B_130,k2_tarski(A_132,B_130)) ),
    inference(resolution,[status(thm)],[c_12,c_499])).

tff(c_461,plain,
    ( '#skF_7' != '#skF_9'
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_463,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_36,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(A_23,k4_xboole_0(B_24,k1_tarski(C_25)))
      | C_25 = A_23
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_498,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_577,plain,(
    ! [B_154,D_155,A_156,C_157] :
      ( r2_hidden(B_154,D_155)
      | ~ r2_hidden(k4_tarski(A_156,B_154),k2_zfmisc_1(C_157,D_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_581,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_498,c_577])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_585,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_7',B_158)
      | ~ r1_tarski(k1_tarski('#skF_9'),B_158) ) ),
    inference(resolution,[status(thm)],[c_581,c_2])).

tff(c_616,plain,(
    ! [B_162] :
      ( r2_hidden('#skF_7',B_162)
      | ~ r2_hidden('#skF_9',B_162) ) ),
    inference(resolution,[status(thm)],[c_22,c_585])).

tff(c_38,plain,(
    ! [C_25,B_24] : ~ r2_hidden(C_25,k4_xboole_0(B_24,k1_tarski(C_25))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_630,plain,(
    ! [B_163] : ~ r2_hidden('#skF_9',k4_xboole_0(B_163,k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_616,c_38])).

tff(c_634,plain,(
    ! [B_24] :
      ( '#skF_7' = '#skF_9'
      | ~ r2_hidden('#skF_9',B_24) ) ),
    inference(resolution,[status(thm)],[c_36,c_630])).

tff(c_638,plain,(
    ! [B_164] : ~ r2_hidden('#skF_9',B_164) ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_634])).

tff(c_654,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_507,c_638])).

tff(c_656,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_656])).

tff(c_678,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_926,plain,(
    ! [A_225,B_226,C_227,D_228] :
      ( r2_hidden(k4_tarski(A_225,B_226),k2_zfmisc_1(C_227,D_228))
      | ~ r2_hidden(B_226,D_228)
      | ~ r2_hidden(A_225,C_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_679,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_655,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_764,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3')))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_48])).

tff(c_765,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_764])).

tff(c_935,plain,
    ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_926,c_765])).

tff(c_946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_75,c_935])).

tff(c_948,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_46,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | '#skF_7' != '#skF_9'
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_959,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_948,c_46])).

tff(c_1262,plain,(
    ! [A_296,B_297,C_298,D_299] :
      ( r2_hidden(k4_tarski(A_296,B_297),k2_zfmisc_1(C_298,D_299))
      | ~ r2_hidden(B_297,D_299)
      | ~ r2_hidden(A_296,C_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_947,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_42,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))
    | '#skF_7' != '#skF_9'
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1204,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_948,c_947,c_42])).

tff(c_1265,plain,
    ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_1262,c_1204])).

tff(c_1277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_75,c_1265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.50  
% 3.42/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.50  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.42/1.50  
% 3.42/1.50  %Foreground sorts:
% 3.42/1.50  
% 3.42/1.50  
% 3.42/1.50  %Background operators:
% 3.42/1.50  
% 3.42/1.50  
% 3.42/1.50  %Foreground operators:
% 3.42/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.42/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.42/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.50  tff('#skF_9', type, '#skF_9': $i).
% 3.42/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.42/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.50  
% 3.42/1.52  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.42/1.52  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.42/1.52  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.52  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.42/1.52  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.42/1.52  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.42/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.42/1.52  tff(c_44, plain, ('#skF_5'='#skF_3' | '#skF_7'!='#skF_9' | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.52  tff(c_86, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_44])).
% 3.42/1.52  tff(c_50, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.52  tff(c_148, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_50])).
% 3.42/1.52  tff(c_185, plain, (![A_67, C_68, B_69, D_70]: (r2_hidden(A_67, C_68) | ~r2_hidden(k4_tarski(A_67, B_69), k2_zfmisc_1(C_68, D_70)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.52  tff(c_188, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_148, c_185])).
% 3.42/1.52  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_188])).
% 3.42/1.52  tff(c_194, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.52  tff(c_52, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.52  tff(c_212, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_194, c_52])).
% 3.42/1.52  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.52  tff(c_66, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | ~r1_tarski(k1_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.42/1.52  tff(c_75, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(resolution, [status(thm)], [c_12, c_66])).
% 3.42/1.52  tff(c_24, plain, (![A_16, B_17, C_18, D_19]: (r2_hidden(k4_tarski(A_16, B_17), k2_zfmisc_1(C_18, D_19)) | ~r2_hidden(B_17, D_19) | ~r2_hidden(A_16, C_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.52  tff(c_193, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.52  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.52  tff(c_452, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3'))) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_48])).
% 3.42/1.52  tff(c_453, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_194, c_452])).
% 3.42/1.52  tff(c_456, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_453])).
% 3.42/1.52  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_75, c_456])).
% 3.42/1.52  tff(c_462, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 3.42/1.52  tff(c_657, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_52])).
% 3.42/1.52  tff(c_499, plain, (![B_130, C_131, A_132]: (r2_hidden(B_130, C_131) | ~r1_tarski(k2_tarski(A_132, B_130), C_131))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.42/1.52  tff(c_507, plain, (![B_130, A_132]: (r2_hidden(B_130, k2_tarski(A_132, B_130)))), inference(resolution, [status(thm)], [c_12, c_499])).
% 3.42/1.52  tff(c_461, plain, ('#skF_7'!='#skF_9' | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 3.42/1.52  tff(c_463, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_461])).
% 3.42/1.52  tff(c_36, plain, (![A_23, B_24, C_25]: (r2_hidden(A_23, k4_xboole_0(B_24, k1_tarski(C_25))) | C_25=A_23 | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.52  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.42/1.52  tff(c_498, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_50])).
% 3.42/1.52  tff(c_577, plain, (![B_154, D_155, A_156, C_157]: (r2_hidden(B_154, D_155) | ~r2_hidden(k4_tarski(A_156, B_154), k2_zfmisc_1(C_157, D_155)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.52  tff(c_581, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_498, c_577])).
% 3.42/1.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.52  tff(c_585, plain, (![B_158]: (r2_hidden('#skF_7', B_158) | ~r1_tarski(k1_tarski('#skF_9'), B_158))), inference(resolution, [status(thm)], [c_581, c_2])).
% 3.42/1.52  tff(c_616, plain, (![B_162]: (r2_hidden('#skF_7', B_162) | ~r2_hidden('#skF_9', B_162))), inference(resolution, [status(thm)], [c_22, c_585])).
% 3.42/1.52  tff(c_38, plain, (![C_25, B_24]: (~r2_hidden(C_25, k4_xboole_0(B_24, k1_tarski(C_25))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.52  tff(c_630, plain, (![B_163]: (~r2_hidden('#skF_9', k4_xboole_0(B_163, k1_tarski('#skF_7'))))), inference(resolution, [status(thm)], [c_616, c_38])).
% 3.42/1.52  tff(c_634, plain, (![B_24]: ('#skF_7'='#skF_9' | ~r2_hidden('#skF_9', B_24))), inference(resolution, [status(thm)], [c_36, c_630])).
% 3.42/1.52  tff(c_638, plain, (![B_164]: (~r2_hidden('#skF_9', B_164))), inference(negUnitSimplification, [status(thm)], [c_463, c_634])).
% 3.42/1.52  tff(c_654, plain, $false, inference(resolution, [status(thm)], [c_507, c_638])).
% 3.42/1.52  tff(c_656, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.52  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_657, c_656])).
% 3.42/1.52  tff(c_678, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.42/1.52  tff(c_926, plain, (![A_225, B_226, C_227, D_228]: (r2_hidden(k4_tarski(A_225, B_226), k2_zfmisc_1(C_227, D_228)) | ~r2_hidden(B_226, D_228) | ~r2_hidden(A_225, C_227))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.52  tff(c_679, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_52])).
% 3.42/1.52  tff(c_655, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.52  tff(c_764, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3'))) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_48])).
% 3.42/1.52  tff(c_765, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_679, c_764])).
% 3.42/1.52  tff(c_935, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_926, c_765])).
% 3.42/1.52  tff(c_946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_678, c_75, c_935])).
% 3.42/1.52  tff(c_948, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_461])).
% 3.42/1.52  tff(c_46, plain, (r2_hidden('#skF_2', '#skF_4') | '#skF_7'!='#skF_9' | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.52  tff(c_959, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_948, c_46])).
% 3.42/1.52  tff(c_1262, plain, (![A_296, B_297, C_298, D_299]: (r2_hidden(k4_tarski(A_296, B_297), k2_zfmisc_1(C_298, D_299)) | ~r2_hidden(B_297, D_299) | ~r2_hidden(A_296, C_298))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.52  tff(c_947, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_461])).
% 3.42/1.52  tff(c_42, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))) | '#skF_7'!='#skF_9' | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.52  tff(c_1204, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_948, c_947, c_42])).
% 3.42/1.52  tff(c_1265, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_1262, c_1204])).
% 3.42/1.52  tff(c_1277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_959, c_75, c_1265])).
% 3.42/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.52  
% 3.42/1.52  Inference rules
% 3.42/1.52  ----------------------
% 3.42/1.52  #Ref     : 0
% 3.42/1.52  #Sup     : 261
% 3.42/1.52  #Fact    : 0
% 3.42/1.52  #Define  : 0
% 3.42/1.52  #Split   : 6
% 3.42/1.52  #Chain   : 0
% 3.42/1.52  #Close   : 0
% 3.42/1.52  
% 3.42/1.52  Ordering : KBO
% 3.42/1.52  
% 3.42/1.52  Simplification rules
% 3.42/1.52  ----------------------
% 3.42/1.52  #Subsume      : 44
% 3.42/1.52  #Demod        : 47
% 3.42/1.52  #Tautology    : 79
% 3.42/1.52  #SimpNegUnit  : 5
% 3.42/1.52  #BackRed      : 0
% 3.42/1.52  
% 3.42/1.52  #Partial instantiations: 0
% 3.42/1.52  #Strategies tried      : 1
% 3.42/1.52  
% 3.42/1.52  Timing (in seconds)
% 3.42/1.52  ----------------------
% 3.42/1.52  Preprocessing        : 0.31
% 3.42/1.52  Parsing              : 0.16
% 3.42/1.52  CNF conversion       : 0.02
% 3.42/1.52  Main loop            : 0.46
% 3.42/1.52  Inferencing          : 0.18
% 3.42/1.52  Reduction            : 0.12
% 3.42/1.52  Demodulation         : 0.09
% 3.42/1.52  BG Simplification    : 0.02
% 3.42/1.52  Subsumption          : 0.09
% 3.42/1.52  Abstraction          : 0.02
% 3.42/1.52  MUC search           : 0.00
% 3.42/1.52  Cooper               : 0.00
% 3.42/1.52  Total                : 0.80
% 3.42/1.52  Index Insertion      : 0.00
% 3.42/1.52  Index Deletion       : 0.00
% 3.42/1.52  Index Matching       : 0.00
% 3.42/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
