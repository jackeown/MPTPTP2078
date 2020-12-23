%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 150 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 276 expanded)
%              Number of equality atoms :   31 ( 159 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16))
      | ~ r2_hidden(B_14,D_16)
      | ~ r2_hidden(A_13,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_93,plain,(
    ! [A_28,C_29,B_30,D_31] :
      ( r2_hidden(A_28,C_29)
      | ~ r2_hidden(k4_tarski(A_28,B_30),k2_zfmisc_1(C_29,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_92,c_93])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_100])).

tff(c_106,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( '#skF_6' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_48])).

tff(c_105,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_182,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_105,c_46])).

tff(c_183,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_182])).

tff(c_186,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_183])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_186])).

tff(c_192,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_191,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_197,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_223,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_50])).

tff(c_224,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_36,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_231,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_224,c_36])).

tff(c_236,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_231,c_2])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_236])).

tff(c_242,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_247,plain,
    ( '#skF_6' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_48])).

tff(c_248,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_247])).

tff(c_241,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_282,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_248,c_241,c_46])).

tff(c_283,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_282])).

tff(c_286,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_283])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_286])).

tff(c_292,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_42,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_302,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_292,c_42])).

tff(c_291,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8')))
    | '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_365,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_292,c_302,c_291,c_40])).

tff(c_368,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_365])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:16:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.40  
% 2.36/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.41  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 2.36/1.41  
% 2.36/1.41  %Foreground sorts:
% 2.36/1.41  
% 2.36/1.41  
% 2.36/1.41  %Background operators:
% 2.36/1.41  
% 2.36/1.41  
% 2.36/1.41  %Foreground operators:
% 2.36/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.41  tff('#skF_11', type, '#skF_11': $i).
% 2.36/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.36/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.41  tff('#skF_10', type, '#skF_10': $i).
% 2.36/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.36/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.36/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.41  tff('#skF_12', type, '#skF_12': $i).
% 2.36/1.41  
% 2.36/1.42  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.36/1.42  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.36/1.42  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.36/1.42  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.42  tff(c_34, plain, (![A_13, B_14, C_15, D_16]: (r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)) | ~r2_hidden(B_14, D_16) | ~r2_hidden(A_13, C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.42  tff(c_44, plain, ('#skF_7'='#skF_5' | '#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.42  tff(c_71, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_44])).
% 2.36/1.42  tff(c_50, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.42  tff(c_92, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_50])).
% 2.36/1.42  tff(c_93, plain, (![A_28, C_29, B_30, D_31]: (r2_hidden(A_28, C_29) | ~r2_hidden(k4_tarski(A_28, B_30), k2_zfmisc_1(C_29, D_31)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.42  tff(c_97, plain, (r2_hidden('#skF_9', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_92, c_93])).
% 2.36/1.42  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.42  tff(c_100, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.36/1.42  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_100])).
% 2.36/1.42  tff(c_106, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_50])).
% 2.36/1.42  tff(c_48, plain, ('#skF_6'='#skF_8' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.42  tff(c_114, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_106, c_48])).
% 2.36/1.42  tff(c_105, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 2.36/1.42  tff(c_46, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.42  tff(c_182, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_105, c_46])).
% 2.36/1.42  tff(c_183, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_106, c_182])).
% 2.36/1.42  tff(c_186, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_183])).
% 2.36/1.42  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_186])).
% 2.36/1.42  tff(c_192, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 2.36/1.42  tff(c_191, plain, ('#skF_10'!='#skF_12' | '#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 2.36/1.42  tff(c_197, plain, ('#skF_10'!='#skF_12'), inference(splitLeft, [status(thm)], [c_191])).
% 2.36/1.42  tff(c_223, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_50])).
% 2.36/1.42  tff(c_224, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_223])).
% 2.36/1.42  tff(c_36, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.42  tff(c_231, plain, (r2_hidden('#skF_10', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_224, c_36])).
% 2.36/1.42  tff(c_236, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_231, c_2])).
% 2.36/1.42  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_236])).
% 2.36/1.42  tff(c_242, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_223])).
% 2.36/1.42  tff(c_247, plain, ('#skF_6'='#skF_8' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_48])).
% 2.36/1.42  tff(c_248, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_242, c_247])).
% 2.36/1.42  tff(c_241, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_223])).
% 2.36/1.42  tff(c_282, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_248, c_241, c_46])).
% 2.36/1.42  tff(c_283, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_242, c_282])).
% 2.36/1.42  tff(c_286, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_283])).
% 2.36/1.42  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_286])).
% 2.36/1.42  tff(c_292, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_191])).
% 2.36/1.42  tff(c_42, plain, ('#skF_6'='#skF_8' | '#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.42  tff(c_302, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_292, c_42])).
% 2.36/1.42  tff(c_291, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_191])).
% 2.36/1.42  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8'))) | '#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.42  tff(c_365, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_292, c_302, c_291, c_40])).
% 2.36/1.42  tff(c_368, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_365])).
% 2.36/1.42  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_368])).
% 2.36/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.42  
% 2.36/1.42  Inference rules
% 2.36/1.42  ----------------------
% 2.36/1.42  #Ref     : 0
% 2.36/1.42  #Sup     : 63
% 2.36/1.42  #Fact    : 0
% 2.36/1.42  #Define  : 0
% 2.36/1.42  #Split   : 5
% 2.36/1.42  #Chain   : 0
% 2.36/1.42  #Close   : 0
% 2.36/1.42  
% 2.36/1.42  Ordering : KBO
% 2.36/1.42  
% 2.36/1.42  Simplification rules
% 2.36/1.42  ----------------------
% 2.36/1.42  #Subsume      : 7
% 2.36/1.42  #Demod        : 37
% 2.36/1.42  #Tautology    : 43
% 2.36/1.42  #SimpNegUnit  : 6
% 2.36/1.42  #BackRed      : 0
% 2.36/1.42  
% 2.36/1.42  #Partial instantiations: 0
% 2.36/1.42  #Strategies tried      : 1
% 2.36/1.42  
% 2.36/1.42  Timing (in seconds)
% 2.36/1.42  ----------------------
% 2.36/1.42  Preprocessing        : 0.35
% 2.36/1.42  Parsing              : 0.18
% 2.36/1.42  CNF conversion       : 0.03
% 2.36/1.42  Main loop            : 0.27
% 2.36/1.42  Inferencing          : 0.10
% 2.36/1.42  Reduction            : 0.07
% 2.36/1.42  Demodulation         : 0.05
% 2.36/1.42  BG Simplification    : 0.02
% 2.36/1.42  Subsumption          : 0.05
% 2.36/1.42  Abstraction          : 0.02
% 2.36/1.42  MUC search           : 0.00
% 2.36/1.42  Cooper               : 0.00
% 2.36/1.42  Total                : 0.65
% 2.36/1.42  Index Insertion      : 0.00
% 2.36/1.42  Index Deletion       : 0.00
% 2.36/1.42  Index Matching       : 0.00
% 2.36/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
