%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 133 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 187 expanded)
%              Number of equality atoms :   33 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6')
    | k7_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_146,plain,(
    k7_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_54])).

tff(c_327,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(k1_relat_1(B_115),A_116) = k1_relat_1(k7_relat_1(B_115,A_116))
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_110,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = k1_xboole_0
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    k3_xboole_0(k1_relat_1('#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_110])).

tff(c_342,plain,
    ( k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_117])).

tff(c_359,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_342])).

tff(c_44,plain,(
    ! [A_63,B_64] :
      ( v1_relat_1(k7_relat_1(A_63,B_64))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [B_67,A_66] :
      ( k3_xboole_0(k1_relat_1(B_67),A_66) = k1_relat_1(k7_relat_1(B_67,A_66))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_366,plain,(
    ! [A_66] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_7','#skF_6'),A_66)) = k3_xboole_0(k1_xboole_0,A_66)
      | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_50])).

tff(c_371,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_374])).

tff(c_380,plain,(
    v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_48,plain,(
    ! [A_65] :
      ( k1_relat_1(A_65) != k1_xboole_0
      | k1_xboole_0 = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_383,plain,
    ( k1_relat_1(k7_relat_1('#skF_7','#skF_6')) != k1_xboole_0
    | k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_380,c_48])).

tff(c_389,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_383])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_389])).

tff(c_392,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_574,plain,(
    ! [B_150,A_151] :
      ( k3_xboole_0(k1_relat_1(B_150),A_151) = k1_relat_1(k7_relat_1(B_150,A_151))
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_408,plain,(
    ! [A_117,B_118] :
      ( r1_xboole_0(A_117,B_118)
      | k3_xboole_0(A_117,B_118) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_393,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_412,plain,(
    k3_xboole_0(k1_relat_1('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_408,c_393])).

tff(c_586,plain,
    ( k1_relat_1(k7_relat_1('#skF_7','#skF_6')) != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_412])).

tff(c_600,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_392,c_586])).

tff(c_990,plain,(
    ! [A_233,B_234] :
      ( r2_hidden(k4_tarski('#skF_2'(A_233,B_234),'#skF_3'(A_233,B_234)),A_233)
      | r2_hidden('#skF_4'(A_233,B_234),B_234)
      | k1_relat_1(A_233) = B_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_430,plain,(
    ! [A_120,B_121] :
      ( k3_xboole_0(A_120,B_121) = k1_xboole_0
      | ~ r1_xboole_0(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_438,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_430])).

tff(c_446,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_xboole_0(A_124,B_125)
      | ~ r2_hidden(C_126,k3_xboole_0(A_124,B_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_449,plain,(
    ! [A_13,B_14,C_126] :
      ( ~ r1_xboole_0(k4_xboole_0(A_13,B_14),B_14)
      | ~ r2_hidden(C_126,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_446])).

tff(c_454,plain,(
    ! [C_126] : ~ r2_hidden(C_126,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_449])).

tff(c_1099,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_235),B_235)
      | k1_relat_1(k1_xboole_0) = B_235 ) ),
    inference(resolution,[status(thm)],[c_990,c_454])).

tff(c_1178,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1099,c_454])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_1178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.19/1.48  
% 3.19/1.48  %Foreground sorts:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Background operators:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Foreground operators:
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.19/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.19/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.19/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.19/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.19/1.48  
% 3.19/1.49  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.19/1.49  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.19/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.19/1.49  tff(f_77, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.19/1.49  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.19/1.49  tff(f_73, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.19/1.49  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.19/1.49  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.19/1.49  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.19/1.49  tff(c_60, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.19/1.49  tff(c_109, plain, (r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_60])).
% 3.19/1.49  tff(c_54, plain, (~r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6') | k7_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.19/1.49  tff(c_146, plain, (k7_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_54])).
% 3.19/1.49  tff(c_327, plain, (![B_115, A_116]: (k3_xboole_0(k1_relat_1(B_115), A_116)=k1_relat_1(k7_relat_1(B_115, A_116)) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.49  tff(c_110, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=k1_xboole_0 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.49  tff(c_117, plain, (k3_xboole_0(k1_relat_1('#skF_7'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_110])).
% 3.19/1.49  tff(c_342, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_327, c_117])).
% 3.19/1.49  tff(c_359, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_342])).
% 3.19/1.49  tff(c_44, plain, (![A_63, B_64]: (v1_relat_1(k7_relat_1(A_63, B_64)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.49  tff(c_50, plain, (![B_67, A_66]: (k3_xboole_0(k1_relat_1(B_67), A_66)=k1_relat_1(k7_relat_1(B_67, A_66)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.49  tff(c_366, plain, (![A_66]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_7', '#skF_6'), A_66))=k3_xboole_0(k1_xboole_0, A_66) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_359, c_50])).
% 3.19/1.49  tff(c_371, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_366])).
% 3.19/1.49  tff(c_374, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_371])).
% 3.19/1.49  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_374])).
% 3.19/1.49  tff(c_380, plain, (v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_366])).
% 3.19/1.49  tff(c_48, plain, (![A_65]: (k1_relat_1(A_65)!=k1_xboole_0 | k1_xboole_0=A_65 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.19/1.49  tff(c_383, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))!=k1_xboole_0 | k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_380, c_48])).
% 3.19/1.49  tff(c_389, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_359, c_383])).
% 3.19/1.49  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_389])).
% 3.19/1.49  tff(c_392, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.19/1.49  tff(c_574, plain, (![B_150, A_151]: (k3_xboole_0(k1_relat_1(B_150), A_151)=k1_relat_1(k7_relat_1(B_150, A_151)) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.49  tff(c_408, plain, (![A_117, B_118]: (r1_xboole_0(A_117, B_118) | k3_xboole_0(A_117, B_118)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.49  tff(c_393, plain, (~r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 3.19/1.49  tff(c_412, plain, (k3_xboole_0(k1_relat_1('#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_408, c_393])).
% 3.19/1.49  tff(c_586, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_574, c_412])).
% 3.19/1.49  tff(c_600, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_392, c_586])).
% 3.19/1.49  tff(c_990, plain, (![A_233, B_234]: (r2_hidden(k4_tarski('#skF_2'(A_233, B_234), '#skF_3'(A_233, B_234)), A_233) | r2_hidden('#skF_4'(A_233, B_234), B_234) | k1_relat_1(A_233)=B_234)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.19/1.49  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.49  tff(c_430, plain, (![A_120, B_121]: (k3_xboole_0(A_120, B_121)=k1_xboole_0 | ~r1_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.49  tff(c_438, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_430])).
% 3.19/1.49  tff(c_446, plain, (![A_124, B_125, C_126]: (~r1_xboole_0(A_124, B_125) | ~r2_hidden(C_126, k3_xboole_0(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.49  tff(c_449, plain, (![A_13, B_14, C_126]: (~r1_xboole_0(k4_xboole_0(A_13, B_14), B_14) | ~r2_hidden(C_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_438, c_446])).
% 3.19/1.49  tff(c_454, plain, (![C_126]: (~r2_hidden(C_126, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_449])).
% 3.19/1.49  tff(c_1099, plain, (![B_235]: (r2_hidden('#skF_4'(k1_xboole_0, B_235), B_235) | k1_relat_1(k1_xboole_0)=B_235)), inference(resolution, [status(thm)], [c_990, c_454])).
% 3.19/1.49  tff(c_1178, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1099, c_454])).
% 3.19/1.49  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_600, c_1178])).
% 3.19/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  Inference rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Ref     : 0
% 3.19/1.49  #Sup     : 251
% 3.19/1.49  #Fact    : 0
% 3.19/1.49  #Define  : 0
% 3.19/1.49  #Split   : 5
% 3.19/1.49  #Chain   : 0
% 3.19/1.49  #Close   : 0
% 3.19/1.49  
% 3.19/1.49  Ordering : KBO
% 3.19/1.49  
% 3.19/1.49  Simplification rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Subsume      : 24
% 3.19/1.49  #Demod        : 79
% 3.19/1.49  #Tautology    : 101
% 3.19/1.49  #SimpNegUnit  : 7
% 3.19/1.49  #BackRed      : 0
% 3.19/1.49  
% 3.19/1.49  #Partial instantiations: 0
% 3.19/1.49  #Strategies tried      : 1
% 3.19/1.49  
% 3.19/1.49  Timing (in seconds)
% 3.19/1.49  ----------------------
% 3.19/1.49  Preprocessing        : 0.34
% 3.19/1.49  Parsing              : 0.18
% 3.19/1.49  CNF conversion       : 0.02
% 3.19/1.49  Main loop            : 0.40
% 3.19/1.49  Inferencing          : 0.15
% 3.19/1.49  Reduction            : 0.12
% 3.19/1.49  Demodulation         : 0.08
% 3.19/1.49  BG Simplification    : 0.02
% 3.19/1.49  Subsumption          : 0.07
% 3.19/1.49  Abstraction          : 0.02
% 3.19/1.49  MUC search           : 0.00
% 3.19/1.49  Cooper               : 0.00
% 3.19/1.49  Total                : 0.76
% 3.19/1.49  Index Insertion      : 0.00
% 3.19/1.49  Index Deletion       : 0.00
% 3.19/1.49  Index Matching       : 0.00
% 3.19/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
