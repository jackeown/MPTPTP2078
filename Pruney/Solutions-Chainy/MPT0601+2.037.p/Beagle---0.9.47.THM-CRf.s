%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 7.30s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 133 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 229 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3544,plain,(
    ! [C_223,B_224,A_225] :
      ( r2_hidden(C_223,B_224)
      | ~ r2_hidden(C_223,A_225)
      | ~ r1_tarski(A_225,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3597,plain,(
    ! [A_230,B_231] :
      ( r2_hidden('#skF_1'(A_230),B_231)
      | ~ r1_tarski(A_230,B_231)
      | v1_xboole_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_4,c_3544])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3615,plain,(
    ! [B_232,A_233] :
      ( ~ v1_xboole_0(B_232)
      | ~ r1_tarski(A_233,B_232)
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_3597,c_2])).

tff(c_3627,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(A_12)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_3615])).

tff(c_3628,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitLeft,[status(thm)],[c_3627])).

tff(c_3555,plain,(
    ! [A_1,B_224] :
      ( r2_hidden('#skF_1'(A_1),B_224)
      | ~ r1_tarski(A_1,B_224)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_3544])).

tff(c_3648,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_1'(A_239),B_240)
      | ~ r1_tarski(A_239,B_240) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3628,c_3555])).

tff(c_18,plain,(
    ! [C_15,B_14] : ~ r2_hidden(C_15,k4_xboole_0(B_14,k1_tarski(C_15))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3693,plain,(
    ! [A_246,B_247] : ~ r1_tarski(A_246,k4_xboole_0(B_247,k1_tarski('#skF_1'(A_246)))) ),
    inference(resolution,[status(thm)],[c_3648,c_18])).

tff(c_3698,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_3693])).

tff(c_3699,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3627])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3880,plain,(
    ! [C_276,A_277] :
      ( r2_hidden(k4_tarski(C_276,'#skF_7'(A_277,k1_relat_1(A_277),C_276)),A_277)
      | ~ r2_hidden(C_276,k1_relat_1(A_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3906,plain,(
    ! [A_278,C_279] :
      ( ~ v1_xboole_0(A_278)
      | ~ r2_hidden(C_279,k1_relat_1(A_278)) ) ),
    inference(resolution,[status(thm)],[c_3880,c_2])).

tff(c_3960,plain,(
    ! [A_281] :
      ( ~ v1_xboole_0(A_281)
      | k1_relat_1(A_281) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_3906])).

tff(c_3972,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3699,c_3960])).

tff(c_3905,plain,(
    ! [A_277,C_276] :
      ( ~ v1_xboole_0(A_277)
      | ~ r2_hidden(C_276,k1_relat_1(A_277)) ) ),
    inference(resolution,[status(thm)],[c_3880,c_2])).

tff(c_4002,plain,(
    ! [C_276] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_276,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3972,c_3905])).

tff(c_4011,plain,(
    ! [C_276] : ~ r2_hidden(C_276,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_4002])).

tff(c_46,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_229,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k4_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,k11_relat_1(C_82,A_80))
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1413,plain,(
    ! [A_159,C_160,B_161] :
      ( r2_hidden(A_159,k1_relat_1(C_160))
      | ~ r2_hidden(B_161,k11_relat_1(C_160,A_159))
      | ~ v1_relat_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_229,c_24])).

tff(c_3362,plain,(
    ! [A_204,C_205] :
      ( r2_hidden(A_204,k1_relat_1(C_205))
      | ~ v1_relat_1(C_205)
      | v1_xboole_0(k11_relat_1(C_205,A_204)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1413])).

tff(c_40,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_40])).

tff(c_3400,plain,
    ( ~ v1_relat_1('#skF_9')
    | v1_xboole_0(k11_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_3362,c_62])).

tff(c_3440,plain,(
    v1_xboole_0(k11_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3400])).

tff(c_49,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_3'(A_41),A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_3490,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3440,c_53])).

tff(c_3500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_3490])).

tff(c_3501,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3508,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3501,c_40])).

tff(c_36,plain,(
    ! [B_36,C_37,A_35] :
      ( r2_hidden(B_36,k11_relat_1(C_37,A_35))
      | ~ r2_hidden(k4_tarski(A_35,B_36),C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10614,plain,(
    ! [A_444,C_445] :
      ( r2_hidden('#skF_7'(A_444,k1_relat_1(A_444),C_445),k11_relat_1(A_444,C_445))
      | ~ v1_relat_1(A_444)
      | ~ r2_hidden(C_445,k1_relat_1(A_444)) ) ),
    inference(resolution,[status(thm)],[c_3880,c_36])).

tff(c_10663,plain,
    ( r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3508,c_10614])).

tff(c_10670,plain,(
    r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3501,c_38,c_10663])).

tff(c_10672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4011,c_10670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:29:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.30/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.54  
% 7.30/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.54  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 7.30/2.54  
% 7.30/2.54  %Foreground sorts:
% 7.30/2.54  
% 7.30/2.54  
% 7.30/2.54  %Background operators:
% 7.30/2.54  
% 7.30/2.54  
% 7.30/2.54  %Foreground operators:
% 7.30/2.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.30/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.30/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.30/2.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.30/2.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.30/2.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.30/2.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.30/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.30/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.30/2.54  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 7.30/2.54  tff('#skF_9', type, '#skF_9': $i).
% 7.30/2.54  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.30/2.54  tff('#skF_8', type, '#skF_8': $i).
% 7.30/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.30/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.30/2.54  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.30/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.30/2.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.30/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.30/2.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.30/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.30/2.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.30/2.54  
% 7.30/2.55  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.30/2.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.30/2.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.30/2.55  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.30/2.55  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.30/2.55  tff(f_63, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 7.30/2.55  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 7.30/2.55  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 7.30/2.55  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.30/2.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.55  tff(c_3544, plain, (![C_223, B_224, A_225]: (r2_hidden(C_223, B_224) | ~r2_hidden(C_223, A_225) | ~r1_tarski(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.30/2.55  tff(c_3597, plain, (![A_230, B_231]: (r2_hidden('#skF_1'(A_230), B_231) | ~r1_tarski(A_230, B_231) | v1_xboole_0(A_230))), inference(resolution, [status(thm)], [c_4, c_3544])).
% 7.30/2.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.55  tff(c_3615, plain, (![B_232, A_233]: (~v1_xboole_0(B_232) | ~r1_tarski(A_233, B_232) | v1_xboole_0(A_233))), inference(resolution, [status(thm)], [c_3597, c_2])).
% 7.30/2.55  tff(c_3627, plain, (![A_12]: (~v1_xboole_0(A_12) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_3615])).
% 7.30/2.55  tff(c_3628, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitLeft, [status(thm)], [c_3627])).
% 7.30/2.55  tff(c_3555, plain, (![A_1, B_224]: (r2_hidden('#skF_1'(A_1), B_224) | ~r1_tarski(A_1, B_224) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_3544])).
% 7.30/2.55  tff(c_3648, plain, (![A_239, B_240]: (r2_hidden('#skF_1'(A_239), B_240) | ~r1_tarski(A_239, B_240))), inference(negUnitSimplification, [status(thm)], [c_3628, c_3555])).
% 7.30/2.55  tff(c_18, plain, (![C_15, B_14]: (~r2_hidden(C_15, k4_xboole_0(B_14, k1_tarski(C_15))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.30/2.55  tff(c_3693, plain, (![A_246, B_247]: (~r1_tarski(A_246, k4_xboole_0(B_247, k1_tarski('#skF_1'(A_246)))))), inference(resolution, [status(thm)], [c_3648, c_18])).
% 7.30/2.55  tff(c_3698, plain, $false, inference(resolution, [status(thm)], [c_14, c_3693])).
% 7.30/2.55  tff(c_3699, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_3627])).
% 7.30/2.55  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.30/2.55  tff(c_3880, plain, (![C_276, A_277]: (r2_hidden(k4_tarski(C_276, '#skF_7'(A_277, k1_relat_1(A_277), C_276)), A_277) | ~r2_hidden(C_276, k1_relat_1(A_277)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.30/2.55  tff(c_3906, plain, (![A_278, C_279]: (~v1_xboole_0(A_278) | ~r2_hidden(C_279, k1_relat_1(A_278)))), inference(resolution, [status(thm)], [c_3880, c_2])).
% 7.30/2.55  tff(c_3960, plain, (![A_281]: (~v1_xboole_0(A_281) | k1_relat_1(A_281)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_3906])).
% 7.30/2.55  tff(c_3972, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3699, c_3960])).
% 7.30/2.55  tff(c_3905, plain, (![A_277, C_276]: (~v1_xboole_0(A_277) | ~r2_hidden(C_276, k1_relat_1(A_277)))), inference(resolution, [status(thm)], [c_3880, c_2])).
% 7.30/2.55  tff(c_4002, plain, (![C_276]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_276, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3972, c_3905])).
% 7.30/2.55  tff(c_4011, plain, (![C_276]: (~r2_hidden(C_276, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_4002])).
% 7.30/2.55  tff(c_46, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9')) | k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.30/2.55  tff(c_61, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 7.30/2.55  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.30/2.55  tff(c_229, plain, (![A_80, B_81, C_82]: (r2_hidden(k4_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, k11_relat_1(C_82, A_80)) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.30/2.55  tff(c_24, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.30/2.55  tff(c_1413, plain, (![A_159, C_160, B_161]: (r2_hidden(A_159, k1_relat_1(C_160)) | ~r2_hidden(B_161, k11_relat_1(C_160, A_159)) | ~v1_relat_1(C_160))), inference(resolution, [status(thm)], [c_229, c_24])).
% 7.30/2.55  tff(c_3362, plain, (![A_204, C_205]: (r2_hidden(A_204, k1_relat_1(C_205)) | ~v1_relat_1(C_205) | v1_xboole_0(k11_relat_1(C_205, A_204)))), inference(resolution, [status(thm)], [c_4, c_1413])).
% 7.30/2.55  tff(c_40, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.30/2.55  tff(c_62, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_61, c_40])).
% 7.30/2.55  tff(c_3400, plain, (~v1_relat_1('#skF_9') | v1_xboole_0(k11_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_3362, c_62])).
% 7.30/2.55  tff(c_3440, plain, (v1_xboole_0(k11_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3400])).
% 7.30/2.55  tff(c_49, plain, (![A_41]: (r2_hidden('#skF_3'(A_41), A_41) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.30/2.55  tff(c_53, plain, (![A_41]: (~v1_xboole_0(A_41) | k1_xboole_0=A_41)), inference(resolution, [status(thm)], [c_49, c_2])).
% 7.30/2.55  tff(c_3490, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_3440, c_53])).
% 7.30/2.55  tff(c_3500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_3490])).
% 7.30/2.55  tff(c_3501, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_46])).
% 7.30/2.55  tff(c_3508, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3501, c_40])).
% 7.30/2.55  tff(c_36, plain, (![B_36, C_37, A_35]: (r2_hidden(B_36, k11_relat_1(C_37, A_35)) | ~r2_hidden(k4_tarski(A_35, B_36), C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.30/2.55  tff(c_10614, plain, (![A_444, C_445]: (r2_hidden('#skF_7'(A_444, k1_relat_1(A_444), C_445), k11_relat_1(A_444, C_445)) | ~v1_relat_1(A_444) | ~r2_hidden(C_445, k1_relat_1(A_444)))), inference(resolution, [status(thm)], [c_3880, c_36])).
% 7.30/2.55  tff(c_10663, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0) | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3508, c_10614])).
% 7.30/2.55  tff(c_10670, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3501, c_38, c_10663])).
% 7.30/2.55  tff(c_10672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4011, c_10670])).
% 7.30/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.55  
% 7.30/2.55  Inference rules
% 7.30/2.55  ----------------------
% 7.30/2.55  #Ref     : 0
% 7.30/2.55  #Sup     : 2616
% 7.30/2.55  #Fact    : 0
% 7.30/2.55  #Define  : 0
% 7.30/2.55  #Split   : 6
% 7.30/2.55  #Chain   : 0
% 7.30/2.55  #Close   : 0
% 7.30/2.55  
% 7.30/2.55  Ordering : KBO
% 7.30/2.55  
% 7.30/2.55  Simplification rules
% 7.30/2.55  ----------------------
% 7.30/2.55  #Subsume      : 1018
% 7.30/2.55  #Demod        : 2051
% 7.30/2.55  #Tautology    : 899
% 7.30/2.55  #SimpNegUnit  : 63
% 7.30/2.55  #BackRed      : 5
% 7.30/2.55  
% 7.30/2.55  #Partial instantiations: 0
% 7.30/2.55  #Strategies tried      : 1
% 7.30/2.55  
% 7.30/2.55  Timing (in seconds)
% 7.30/2.55  ----------------------
% 7.30/2.56  Preprocessing        : 0.30
% 7.30/2.56  Parsing              : 0.17
% 7.30/2.56  CNF conversion       : 0.02
% 7.30/2.56  Main loop            : 1.46
% 7.30/2.56  Inferencing          : 0.49
% 7.30/2.56  Reduction            : 0.41
% 7.30/2.56  Demodulation         : 0.27
% 7.30/2.56  BG Simplification    : 0.05
% 7.30/2.56  Subsumption          : 0.42
% 7.30/2.56  Abstraction          : 0.07
% 7.30/2.56  MUC search           : 0.00
% 7.30/2.56  Cooper               : 0.00
% 7.30/2.56  Total                : 1.80
% 7.30/2.56  Index Insertion      : 0.00
% 7.30/2.56  Index Deletion       : 0.00
% 7.30/2.56  Index Matching       : 0.00
% 7.30/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
