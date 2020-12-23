%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 167 expanded)
%              Number of leaves         :   42 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :   77 ( 264 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_90,plain,(
    k1_wellord1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_94,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_825,plain,(
    ! [A_206,B_207,C_208] :
      ( r2_hidden('#skF_3'(A_206,B_207,C_208),B_207)
      | r2_hidden('#skF_4'(A_206,B_207,C_208),C_208)
      | k3_xboole_0(A_206,B_207) = C_208 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_422,plain,(
    ! [A_157,C_158] :
      ( r2_hidden(k4_tarski('#skF_8'(A_157,k2_relat_1(A_157),C_158),C_158),A_157)
      | ~ r2_hidden(C_158,k2_relat_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_70,plain,(
    ! [B_65,A_64] :
      ( ~ r1_tarski(B_65,A_64)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_729,plain,(
    ! [A_193,C_194] :
      ( ~ r1_tarski(A_193,k4_tarski('#skF_8'(A_193,k2_relat_1(A_193),C_194),C_194))
      | ~ r2_hidden(C_194,k2_relat_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_422,c_70])).

tff(c_734,plain,(
    ! [C_194] : ~ r2_hidden(C_194,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_40,c_729])).

tff(c_1108,plain,(
    ! [A_215,C_216] :
      ( r2_hidden('#skF_4'(A_215,k2_relat_1(k1_xboole_0),C_216),C_216)
      | k3_xboole_0(A_215,k2_relat_1(k1_xboole_0)) = C_216 ) ),
    inference(resolution,[status(thm)],[c_825,c_734])).

tff(c_1196,plain,(
    ! [A_215] : k3_xboole_0(A_215,k2_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1108,c_734])).

tff(c_962,plain,(
    ! [A_206,C_208] :
      ( r2_hidden('#skF_4'(A_206,k2_relat_1(k1_xboole_0),C_208),C_208)
      | k3_xboole_0(A_206,k2_relat_1(k1_xboole_0)) = C_208 ) ),
    inference(resolution,[status(thm)],[c_825,c_734])).

tff(c_1396,plain,(
    ! [A_221,C_222] :
      ( r2_hidden('#skF_4'(A_221,k2_relat_1(k1_xboole_0),C_222),C_222)
      | k2_relat_1(k1_xboole_0) = C_222 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_962])).

tff(c_1501,plain,(
    ! [C_226,A_227] :
      ( ~ r1_tarski(C_226,'#skF_4'(A_227,k2_relat_1(k1_xboole_0),C_226))
      | k2_relat_1(k1_xboole_0) = C_226 ) ),
    inference(resolution,[status(thm)],[c_1396,c_70])).

tff(c_1506,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1501])).

tff(c_1210,plain,(
    ! [A_206,C_208] :
      ( r2_hidden('#skF_4'(A_206,k2_relat_1(k1_xboole_0),C_208),C_208)
      | k2_relat_1(k1_xboole_0) = C_208 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_962])).

tff(c_1568,plain,(
    ! [A_229,C_230] :
      ( r2_hidden('#skF_4'(A_229,k1_xboole_0,C_230),C_230)
      | k1_xboole_0 = C_230 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1506,c_1210])).

tff(c_310,plain,(
    ! [D_146,B_147,A_148] :
      ( r2_hidden(k4_tarski(D_146,B_147),A_148)
      | ~ r2_hidden(D_146,k1_wellord1(A_148,B_147))
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    ! [C_59,A_44,D_62] :
      ( r2_hidden(C_59,k2_relat_1(A_44))
      | ~ r2_hidden(k4_tarski(D_62,C_59),A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_357,plain,(
    ! [B_147,A_148,D_146] :
      ( r2_hidden(B_147,k2_relat_1(A_148))
      | ~ r2_hidden(D_146,k1_wellord1(A_148,B_147))
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_310,c_58])).

tff(c_1892,plain,(
    ! [B_244,A_245] :
      ( r2_hidden(B_244,k2_relat_1(A_245))
      | ~ v1_relat_1(A_245)
      | k1_wellord1(A_245,B_244) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1568,c_357])).

tff(c_155,plain,(
    ! [A_111] :
      ( k2_xboole_0(k1_relat_1(A_111),k2_relat_1(A_111)) = k3_relat_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_197,plain,(
    ! [D_118,A_119] :
      ( ~ r2_hidden(D_118,k2_relat_1(A_119))
      | r2_hidden(D_118,k3_relat_1(A_119))
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_4])).

tff(c_92,plain,(
    ~ r2_hidden('#skF_11',k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_207,plain,
    ( ~ r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_197,c_92])).

tff(c_212,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_207])).

tff(c_1933,plain,
    ( ~ v1_relat_1('#skF_12')
    | k1_wellord1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1892,c_212])).

tff(c_1957,plain,(
    k1_wellord1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1933])).

tff(c_1959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.66  
% 3.70/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.66  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12 > #skF_10
% 3.70/1.66  
% 3.70/1.66  %Foreground sorts:
% 3.70/1.66  
% 3.70/1.66  
% 3.70/1.66  %Background operators:
% 3.70/1.66  
% 3.70/1.66  
% 3.70/1.66  %Foreground operators:
% 3.70/1.66  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.70/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.66  tff('#skF_11', type, '#skF_11': $i).
% 3.70/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.70/1.66  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.70/1.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.70/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.70/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.70/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.66  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.70/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.66  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.70/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.66  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.70/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.70/1.66  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.70/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.70/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.66  tff('#skF_12', type, '#skF_12': $i).
% 3.70/1.66  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.70/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.70/1.66  
% 3.90/1.67  tff(f_98, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 3.90/1.67  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.90/1.67  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.90/1.67  tff(f_69, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.90/1.67  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.90/1.67  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 3.90/1.67  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.90/1.67  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.90/1.67  tff(c_90, plain, (k1_wellord1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.90/1.67  tff(c_94, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.90/1.67  tff(c_40, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.90/1.67  tff(c_825, plain, (![A_206, B_207, C_208]: (r2_hidden('#skF_3'(A_206, B_207, C_208), B_207) | r2_hidden('#skF_4'(A_206, B_207, C_208), C_208) | k3_xboole_0(A_206, B_207)=C_208)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.90/1.67  tff(c_422, plain, (![A_157, C_158]: (r2_hidden(k4_tarski('#skF_8'(A_157, k2_relat_1(A_157), C_158), C_158), A_157) | ~r2_hidden(C_158, k2_relat_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/1.67  tff(c_70, plain, (![B_65, A_64]: (~r1_tarski(B_65, A_64) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.90/1.67  tff(c_729, plain, (![A_193, C_194]: (~r1_tarski(A_193, k4_tarski('#skF_8'(A_193, k2_relat_1(A_193), C_194), C_194)) | ~r2_hidden(C_194, k2_relat_1(A_193)))), inference(resolution, [status(thm)], [c_422, c_70])).
% 3.90/1.67  tff(c_734, plain, (![C_194]: (~r2_hidden(C_194, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_40, c_729])).
% 3.90/1.67  tff(c_1108, plain, (![A_215, C_216]: (r2_hidden('#skF_4'(A_215, k2_relat_1(k1_xboole_0), C_216), C_216) | k3_xboole_0(A_215, k2_relat_1(k1_xboole_0))=C_216)), inference(resolution, [status(thm)], [c_825, c_734])).
% 3.90/1.67  tff(c_1196, plain, (![A_215]: (k3_xboole_0(A_215, k2_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1108, c_734])).
% 3.90/1.67  tff(c_962, plain, (![A_206, C_208]: (r2_hidden('#skF_4'(A_206, k2_relat_1(k1_xboole_0), C_208), C_208) | k3_xboole_0(A_206, k2_relat_1(k1_xboole_0))=C_208)), inference(resolution, [status(thm)], [c_825, c_734])).
% 3.90/1.67  tff(c_1396, plain, (![A_221, C_222]: (r2_hidden('#skF_4'(A_221, k2_relat_1(k1_xboole_0), C_222), C_222) | k2_relat_1(k1_xboole_0)=C_222)), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_962])).
% 3.90/1.67  tff(c_1501, plain, (![C_226, A_227]: (~r1_tarski(C_226, '#skF_4'(A_227, k2_relat_1(k1_xboole_0), C_226)) | k2_relat_1(k1_xboole_0)=C_226)), inference(resolution, [status(thm)], [c_1396, c_70])).
% 3.90/1.67  tff(c_1506, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1501])).
% 3.90/1.67  tff(c_1210, plain, (![A_206, C_208]: (r2_hidden('#skF_4'(A_206, k2_relat_1(k1_xboole_0), C_208), C_208) | k2_relat_1(k1_xboole_0)=C_208)), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_962])).
% 3.90/1.67  tff(c_1568, plain, (![A_229, C_230]: (r2_hidden('#skF_4'(A_229, k1_xboole_0, C_230), C_230) | k1_xboole_0=C_230)), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1506, c_1210])).
% 3.90/1.67  tff(c_310, plain, (![D_146, B_147, A_148]: (r2_hidden(k4_tarski(D_146, B_147), A_148) | ~r2_hidden(D_146, k1_wellord1(A_148, B_147)) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.90/1.67  tff(c_58, plain, (![C_59, A_44, D_62]: (r2_hidden(C_59, k2_relat_1(A_44)) | ~r2_hidden(k4_tarski(D_62, C_59), A_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/1.67  tff(c_357, plain, (![B_147, A_148, D_146]: (r2_hidden(B_147, k2_relat_1(A_148)) | ~r2_hidden(D_146, k1_wellord1(A_148, B_147)) | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_310, c_58])).
% 3.90/1.67  tff(c_1892, plain, (![B_244, A_245]: (r2_hidden(B_244, k2_relat_1(A_245)) | ~v1_relat_1(A_245) | k1_wellord1(A_245, B_244)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1568, c_357])).
% 3.90/1.67  tff(c_155, plain, (![A_111]: (k2_xboole_0(k1_relat_1(A_111), k2_relat_1(A_111))=k3_relat_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.90/1.67  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.90/1.67  tff(c_197, plain, (![D_118, A_119]: (~r2_hidden(D_118, k2_relat_1(A_119)) | r2_hidden(D_118, k3_relat_1(A_119)) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_155, c_4])).
% 3.90/1.67  tff(c_92, plain, (~r2_hidden('#skF_11', k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.90/1.67  tff(c_207, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_197, c_92])).
% 3.90/1.67  tff(c_212, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_207])).
% 3.90/1.67  tff(c_1933, plain, (~v1_relat_1('#skF_12') | k1_wellord1('#skF_12', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_1892, c_212])).
% 3.90/1.67  tff(c_1957, plain, (k1_wellord1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1933])).
% 3.90/1.67  tff(c_1959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1957])).
% 3.90/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.67  
% 3.90/1.67  Inference rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Ref     : 0
% 3.90/1.67  #Sup     : 393
% 3.90/1.67  #Fact    : 0
% 3.90/1.67  #Define  : 0
% 3.90/1.67  #Split   : 3
% 3.90/1.67  #Chain   : 0
% 3.90/1.67  #Close   : 0
% 3.90/1.67  
% 3.90/1.67  Ordering : KBO
% 3.90/1.67  
% 3.90/1.67  Simplification rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Subsume      : 53
% 3.90/1.67  #Demod        : 66
% 3.90/1.67  #Tautology    : 42
% 3.90/1.67  #SimpNegUnit  : 6
% 3.90/1.67  #BackRed      : 14
% 3.90/1.67  
% 3.90/1.67  #Partial instantiations: 0
% 3.90/1.67  #Strategies tried      : 1
% 3.90/1.67  
% 3.90/1.67  Timing (in seconds)
% 3.90/1.67  ----------------------
% 3.90/1.68  Preprocessing        : 0.36
% 3.90/1.68  Parsing              : 0.17
% 3.90/1.68  CNF conversion       : 0.03
% 3.90/1.68  Main loop            : 0.52
% 3.90/1.68  Inferencing          : 0.19
% 3.90/1.68  Reduction            : 0.13
% 3.90/1.68  Demodulation         : 0.09
% 3.90/1.68  BG Simplification    : 0.03
% 3.90/1.68  Subsumption          : 0.12
% 3.90/1.68  Abstraction          : 0.04
% 3.90/1.68  MUC search           : 0.00
% 3.90/1.68  Cooper               : 0.00
% 3.90/1.68  Total                : 0.90
% 3.90/1.68  Index Insertion      : 0.00
% 3.90/1.68  Index Deletion       : 0.00
% 3.90/1.68  Index Matching       : 0.00
% 3.90/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
