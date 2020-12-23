%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:02 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 151 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :   97 ( 273 expanded)
%              Number of equality atoms :   20 (  80 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_30,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_79,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( r2_hidden(A_50,C_51)
      | ~ r2_hidden(k4_tarski(A_50,B_52),k2_zfmisc_1(C_51,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_79])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_82])).

tff(c_91,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_38])).

tff(c_22,plain,(
    ! [C_35,D_36] : r2_hidden(k4_tarski(C_35,D_36),k2_zfmisc_1(k1_tarski(C_35),k1_tarski(D_36))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [B_45,D_46,A_47,C_48] :
      ( r2_hidden(B_45,D_46)
      | ~ r2_hidden(k4_tarski(A_47,B_45),k2_zfmisc_1(C_48,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [D_36] : r2_hidden(D_36,k1_tarski(D_36)) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_16,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( r2_hidden(k4_tarski(A_29,B_30),k2_zfmisc_1(C_31,D_32))
      | ~ r2_hidden(B_30,D_32)
      | ~ r2_hidden(A_29,C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_176,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_34])).

tff(c_177,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_176])).

tff(c_180,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_72,c_180])).

tff(c_185,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_193,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_204,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_225,plain,(
    ! [B_99,D_100,A_101,C_102] :
      ( r2_hidden(B_99,D_100)
      | ~ r2_hidden(k4_tarski(A_101,B_99),k2_zfmisc_1(C_102,D_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_232,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_204,c_225])).

tff(c_268,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( r2_hidden(k4_tarski(A_120,B_121),k2_zfmisc_1(C_122,D_123))
      | ~ r2_hidden(B_121,D_123)
      | ~ r2_hidden(A_120,C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [C_35,A_33,B_34,D_36] :
      ( C_35 = A_33
      | ~ r2_hidden(k4_tarski(A_33,B_34),k2_zfmisc_1(k1_tarski(C_35),k1_tarski(D_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_283,plain,(
    ! [C_35,A_120,B_121,D_36] :
      ( C_35 = A_120
      | ~ r2_hidden(B_121,k1_tarski(D_36))
      | ~ r2_hidden(A_120,k1_tarski(C_35)) ) ),
    inference(resolution,[status(thm)],[c_268,c_26])).

tff(c_287,plain,(
    ! [B_121,D_36] : ~ r2_hidden(B_121,k1_tarski(D_36)) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_232])).

tff(c_301,plain,(
    ! [C_130,A_131] :
      ( C_130 = A_131
      | ~ r2_hidden(A_131,k1_tarski(C_130)) ) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_304,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_232,c_301])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_304])).

tff(c_313,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_318,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_38])).

tff(c_328,plain,(
    ! [B_135,D_136,A_137,C_138] :
      ( r2_hidden(B_135,D_136)
      | ~ r2_hidden(k4_tarski(A_137,B_135),k2_zfmisc_1(C_138,D_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_332,plain,(
    ! [D_36] : r2_hidden(D_36,k1_tarski(D_36)) ),
    inference(resolution,[status(thm)],[c_22,c_328])).

tff(c_312,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_416,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_34])).

tff(c_417,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_416])).

tff(c_420,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_417])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_332,c_420])).

tff(c_426,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_186,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_187])).

tff(c_190,plain,
    ( '#skF_6' != '#skF_8'
    | r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_437,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_190])).

tff(c_457,plain,(
    ! [A_180,C_181,B_182,D_183] :
      ( r2_hidden(A_180,C_181)
      | ~ r2_hidden(k4_tarski(A_180,B_182),k2_zfmisc_1(C_181,D_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_461,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(resolution,[status(thm)],[c_22,c_457])).

tff(c_502,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( r2_hidden(k4_tarski(A_206,B_207),k2_zfmisc_1(C_208,D_209))
      | ~ r2_hidden(B_207,D_209)
      | ~ r2_hidden(A_206,C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_425,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_492,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_426,c_425,c_28])).

tff(c_505,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_502,c_492])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_461,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.31  
% 2.43/1.32  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.43/1.32  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.43/1.32  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.43/1.32  tff(c_30, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_48, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_30])).
% 2.43/1.32  tff(c_36, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_74, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.43/1.32  tff(c_79, plain, (![A_50, C_51, B_52, D_53]: (r2_hidden(A_50, C_51) | ~r2_hidden(k4_tarski(A_50, B_52), k2_zfmisc_1(C_51, D_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_82, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_79])).
% 2.43/1.32  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_82])).
% 2.43/1.32  tff(c_91, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_36])).
% 2.43/1.32  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_102, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_91, c_38])).
% 2.43/1.32  tff(c_22, plain, (![C_35, D_36]: (r2_hidden(k4_tarski(C_35, D_36), k2_zfmisc_1(k1_tarski(C_35), k1_tarski(D_36))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.43/1.32  tff(c_68, plain, (![B_45, D_46, A_47, C_48]: (r2_hidden(B_45, D_46) | ~r2_hidden(k4_tarski(A_47, B_45), k2_zfmisc_1(C_48, D_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_72, plain, (![D_36]: (r2_hidden(D_36, k1_tarski(D_36)))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.43/1.32  tff(c_16, plain, (![A_29, B_30, C_31, D_32]: (r2_hidden(k4_tarski(A_29, B_30), k2_zfmisc_1(C_31, D_32)) | ~r2_hidden(B_30, D_32) | ~r2_hidden(A_29, C_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_90, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.43/1.32  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_176, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_34])).
% 2.43/1.32  tff(c_177, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_91, c_176])).
% 2.43/1.32  tff(c_180, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_177])).
% 2.43/1.32  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_72, c_180])).
% 2.43/1.32  tff(c_185, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.43/1.32  tff(c_193, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_185])).
% 2.43/1.32  tff(c_204, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.43/1.32  tff(c_225, plain, (![B_99, D_100, A_101, C_102]: (r2_hidden(B_99, D_100) | ~r2_hidden(k4_tarski(A_101, B_99), k2_zfmisc_1(C_102, D_100)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_232, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_204, c_225])).
% 2.43/1.32  tff(c_268, plain, (![A_120, B_121, C_122, D_123]: (r2_hidden(k4_tarski(A_120, B_121), k2_zfmisc_1(C_122, D_123)) | ~r2_hidden(B_121, D_123) | ~r2_hidden(A_120, C_122))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_26, plain, (![C_35, A_33, B_34, D_36]: (C_35=A_33 | ~r2_hidden(k4_tarski(A_33, B_34), k2_zfmisc_1(k1_tarski(C_35), k1_tarski(D_36))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.43/1.32  tff(c_283, plain, (![C_35, A_120, B_121, D_36]: (C_35=A_120 | ~r2_hidden(B_121, k1_tarski(D_36)) | ~r2_hidden(A_120, k1_tarski(C_35)))), inference(resolution, [status(thm)], [c_268, c_26])).
% 2.43/1.32  tff(c_287, plain, (![B_121, D_36]: (~r2_hidden(B_121, k1_tarski(D_36)))), inference(splitLeft, [status(thm)], [c_283])).
% 2.43/1.32  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_232])).
% 2.43/1.32  tff(c_301, plain, (![C_130, A_131]: (C_130=A_131 | ~r2_hidden(A_131, k1_tarski(C_130)))), inference(splitRight, [status(thm)], [c_283])).
% 2.43/1.32  tff(c_304, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_232, c_301])).
% 2.43/1.32  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_304])).
% 2.43/1.32  tff(c_313, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_36])).
% 2.43/1.32  tff(c_318, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_313, c_38])).
% 2.43/1.32  tff(c_328, plain, (![B_135, D_136, A_137, C_138]: (r2_hidden(B_135, D_136) | ~r2_hidden(k4_tarski(A_137, B_135), k2_zfmisc_1(C_138, D_136)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_332, plain, (![D_36]: (r2_hidden(D_36, k1_tarski(D_36)))), inference(resolution, [status(thm)], [c_22, c_328])).
% 2.43/1.32  tff(c_312, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.43/1.32  tff(c_416, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_34])).
% 2.43/1.32  tff(c_417, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_313, c_416])).
% 2.43/1.32  tff(c_420, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_417])).
% 2.43/1.32  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_332, c_420])).
% 2.43/1.32  tff(c_426, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_185])).
% 2.43/1.32  tff(c_186, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_30])).
% 2.43/1.32  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_187, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_32])).
% 2.43/1.32  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_187])).
% 2.43/1.32  tff(c_190, plain, ('#skF_6'!='#skF_8' | r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.43/1.32  tff(c_437, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_426, c_190])).
% 2.43/1.32  tff(c_457, plain, (![A_180, C_181, B_182, D_183]: (r2_hidden(A_180, C_181) | ~r2_hidden(k4_tarski(A_180, B_182), k2_zfmisc_1(C_181, D_183)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_461, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(resolution, [status(thm)], [c_22, c_457])).
% 2.43/1.32  tff(c_502, plain, (![A_206, B_207, C_208, D_209]: (r2_hidden(k4_tarski(A_206, B_207), k2_zfmisc_1(C_208, D_209)) | ~r2_hidden(B_207, D_209) | ~r2_hidden(A_206, C_208))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_425, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_185])).
% 2.43/1.32  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_492, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_426, c_425, c_28])).
% 2.43/1.32  tff(c_505, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_502, c_492])).
% 2.43/1.32  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_437, c_461, c_505])).
% 2.43/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  Inference rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Ref     : 0
% 2.43/1.32  #Sup     : 92
% 2.43/1.32  #Fact    : 0
% 2.43/1.32  #Define  : 0
% 2.43/1.32  #Split   : 8
% 2.43/1.32  #Chain   : 0
% 2.43/1.32  #Close   : 0
% 2.43/1.32  
% 2.43/1.32  Ordering : KBO
% 2.43/1.32  
% 2.43/1.32  Simplification rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Subsume      : 9
% 2.43/1.32  #Demod        : 29
% 2.43/1.32  #Tautology    : 71
% 2.43/1.32  #SimpNegUnit  : 10
% 2.43/1.32  #BackRed      : 4
% 2.43/1.32  
% 2.43/1.32  #Partial instantiations: 0
% 2.43/1.32  #Strategies tried      : 1
% 2.43/1.32  
% 2.43/1.32  Timing (in seconds)
% 2.43/1.32  ----------------------
% 2.43/1.33  Preprocessing        : 0.31
% 2.43/1.33  Parsing              : 0.16
% 2.43/1.33  CNF conversion       : 0.02
% 2.43/1.33  Main loop            : 0.25
% 2.43/1.33  Inferencing          : 0.10
% 2.43/1.33  Reduction            : 0.07
% 2.43/1.33  Demodulation         : 0.04
% 2.43/1.33  BG Simplification    : 0.01
% 2.43/1.33  Subsumption          : 0.04
% 2.43/1.33  Abstraction          : 0.01
% 2.43/1.33  MUC search           : 0.00
% 2.43/1.33  Cooper               : 0.00
% 2.43/1.33  Total                : 0.59
% 2.43/1.33  Index Insertion      : 0.00
% 2.43/1.33  Index Deletion       : 0.00
% 2.43/1.33  Index Matching       : 0.00
% 2.43/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
