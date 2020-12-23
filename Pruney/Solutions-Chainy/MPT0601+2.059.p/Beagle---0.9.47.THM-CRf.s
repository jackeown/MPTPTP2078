%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 117 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_720,plain,(
    ! [A_163,B_164,C_165] :
      ( ~ r1_xboole_0(A_163,B_164)
      | ~ r2_hidden(C_165,k3_xboole_0(A_163,B_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_723,plain,(
    ! [A_6,C_165] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_165,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_720])).

tff(c_725,plain,(
    ! [C_165] : ~ r2_hidden(C_165,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_723])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_87,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_383,plain,(
    ! [A_152,B_153] :
      ( r2_hidden(k4_tarski('#skF_2'(A_152,B_153),'#skF_3'(A_152,B_153)),A_152)
      | r2_hidden('#skF_4'(A_152,B_153),B_153)
      | k1_relat_1(A_152) = B_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_6,C_67] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_94,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_440,plain,(
    ! [B_153] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_153),B_153)
      | k1_relat_1(k1_xboole_0) = B_153 ) ),
    inference(resolution,[status(thm)],[c_383,c_94])).

tff(c_462,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_154),B_154)
      | k1_xboole_0 = B_154 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_440])).

tff(c_125,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden(k4_tarski(A_81,B_82),C_83)
      | ~ r2_hidden(B_82,k11_relat_1(C_83,A_81))
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [C_52,A_37,D_55] :
      ( r2_hidden(C_52,k1_relat_1(A_37))
      | ~ r2_hidden(k4_tarski(C_52,D_55),A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,(
    ! [A_81,C_83,B_82] :
      ( r2_hidden(A_81,k1_relat_1(C_83))
      | ~ r2_hidden(B_82,k11_relat_1(C_83,A_81))
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_125,c_26])).

tff(c_625,plain,(
    ! [A_161,C_162] :
      ( r2_hidden(A_161,k1_relat_1(C_162))
      | ~ v1_relat_1(C_162)
      | k11_relat_1(C_162,A_161) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_462,c_137])).

tff(c_46,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_46])).

tff(c_683,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_625,c_88])).

tff(c_709,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_683])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_709])).

tff(c_712,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_713,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_787,plain,(
    ! [C_190,A_191] :
      ( r2_hidden(k4_tarski(C_190,'#skF_5'(A_191,k1_relat_1(A_191),C_190)),A_191)
      | ~ r2_hidden(C_190,k1_relat_1(A_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [B_57,C_58,A_56] :
      ( r2_hidden(B_57,k11_relat_1(C_58,A_56))
      | ~ r2_hidden(k4_tarski(A_56,B_57),C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_995,plain,(
    ! [A_237,C_238] :
      ( r2_hidden('#skF_5'(A_237,k1_relat_1(A_237),C_238),k11_relat_1(A_237,C_238))
      | ~ v1_relat_1(A_237)
      | ~ r2_hidden(C_238,k1_relat_1(A_237)) ) ),
    inference(resolution,[status(thm)],[c_787,c_38])).

tff(c_1004,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_995])).

tff(c_1011,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_44,c_1004])).

tff(c_1013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_725,c_1011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 11:46:29 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.77/1.44  
% 2.77/1.44  %Foreground sorts:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Background operators:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Foreground operators:
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.77/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.77/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.77/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.44  
% 2.77/1.46  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.77/1.46  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.77/1.46  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.77/1.46  tff(f_82, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.77/1.46  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.77/1.46  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.77/1.46  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.77/1.46  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.46  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.46  tff(c_720, plain, (![A_163, B_164, C_165]: (~r1_xboole_0(A_163, B_164) | ~r2_hidden(C_165, k3_xboole_0(A_163, B_164)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.46  tff(c_723, plain, (![A_6, C_165]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_165, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_720])).
% 2.77/1.46  tff(c_725, plain, (![C_165]: (~r2_hidden(C_165, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_723])).
% 2.77/1.46  tff(c_52, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.77/1.46  tff(c_87, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.77/1.46  tff(c_44, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.77/1.46  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.46  tff(c_383, plain, (![A_152, B_153]: (r2_hidden(k4_tarski('#skF_2'(A_152, B_153), '#skF_3'(A_152, B_153)), A_152) | r2_hidden('#skF_4'(A_152, B_153), B_153) | k1_relat_1(A_152)=B_153)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.46  tff(c_89, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.46  tff(c_92, plain, (![A_6, C_67]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_89])).
% 2.77/1.46  tff(c_94, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92])).
% 2.77/1.46  tff(c_440, plain, (![B_153]: (r2_hidden('#skF_4'(k1_xboole_0, B_153), B_153) | k1_relat_1(k1_xboole_0)=B_153)), inference(resolution, [status(thm)], [c_383, c_94])).
% 2.77/1.46  tff(c_462, plain, (![B_154]: (r2_hidden('#skF_4'(k1_xboole_0, B_154), B_154) | k1_xboole_0=B_154)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_440])).
% 2.77/1.46  tff(c_125, plain, (![A_81, B_82, C_83]: (r2_hidden(k4_tarski(A_81, B_82), C_83) | ~r2_hidden(B_82, k11_relat_1(C_83, A_81)) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.77/1.46  tff(c_26, plain, (![C_52, A_37, D_55]: (r2_hidden(C_52, k1_relat_1(A_37)) | ~r2_hidden(k4_tarski(C_52, D_55), A_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.46  tff(c_137, plain, (![A_81, C_83, B_82]: (r2_hidden(A_81, k1_relat_1(C_83)) | ~r2_hidden(B_82, k11_relat_1(C_83, A_81)) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_125, c_26])).
% 2.77/1.46  tff(c_625, plain, (![A_161, C_162]: (r2_hidden(A_161, k1_relat_1(C_162)) | ~v1_relat_1(C_162) | k11_relat_1(C_162, A_161)=k1_xboole_0)), inference(resolution, [status(thm)], [c_462, c_137])).
% 2.77/1.46  tff(c_46, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.77/1.46  tff(c_88, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_87, c_46])).
% 2.77/1.46  tff(c_683, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_625, c_88])).
% 2.77/1.46  tff(c_709, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_683])).
% 2.77/1.46  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_709])).
% 2.77/1.46  tff(c_712, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 2.77/1.46  tff(c_713, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.77/1.46  tff(c_787, plain, (![C_190, A_191]: (r2_hidden(k4_tarski(C_190, '#skF_5'(A_191, k1_relat_1(A_191), C_190)), A_191) | ~r2_hidden(C_190, k1_relat_1(A_191)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.46  tff(c_38, plain, (![B_57, C_58, A_56]: (r2_hidden(B_57, k11_relat_1(C_58, A_56)) | ~r2_hidden(k4_tarski(A_56, B_57), C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.77/1.46  tff(c_995, plain, (![A_237, C_238]: (r2_hidden('#skF_5'(A_237, k1_relat_1(A_237), C_238), k11_relat_1(A_237, C_238)) | ~v1_relat_1(A_237) | ~r2_hidden(C_238, k1_relat_1(A_237)))), inference(resolution, [status(thm)], [c_787, c_38])).
% 2.77/1.46  tff(c_1004, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_713, c_995])).
% 2.77/1.46  tff(c_1011, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_712, c_44, c_1004])).
% 2.77/1.46  tff(c_1013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_725, c_1011])).
% 2.77/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.46  
% 2.77/1.46  Inference rules
% 2.77/1.46  ----------------------
% 2.77/1.46  #Ref     : 0
% 2.77/1.46  #Sup     : 197
% 2.77/1.46  #Fact    : 0
% 2.77/1.46  #Define  : 0
% 2.77/1.46  #Split   : 3
% 2.77/1.46  #Chain   : 0
% 2.77/1.46  #Close   : 0
% 2.77/1.46  
% 2.77/1.46  Ordering : KBO
% 2.77/1.46  
% 2.77/1.46  Simplification rules
% 2.77/1.46  ----------------------
% 2.77/1.46  #Subsume      : 41
% 2.77/1.46  #Demod        : 121
% 2.77/1.46  #Tautology    : 52
% 2.77/1.46  #SimpNegUnit  : 7
% 2.77/1.46  #BackRed      : 0
% 2.77/1.46  
% 2.77/1.46  #Partial instantiations: 0
% 2.77/1.46  #Strategies tried      : 1
% 2.77/1.46  
% 2.77/1.46  Timing (in seconds)
% 2.77/1.46  ----------------------
% 2.77/1.46  Preprocessing        : 0.33
% 2.77/1.46  Parsing              : 0.17
% 2.77/1.46  CNF conversion       : 0.02
% 2.77/1.46  Main loop            : 0.35
% 2.77/1.46  Inferencing          : 0.14
% 2.77/1.46  Reduction            : 0.09
% 2.77/1.46  Demodulation         : 0.06
% 2.77/1.46  BG Simplification    : 0.02
% 2.77/1.46  Subsumption          : 0.07
% 2.77/1.46  Abstraction          : 0.02
% 2.77/1.46  MUC search           : 0.00
% 2.77/1.46  Cooper               : 0.00
% 2.77/1.46  Total                : 0.70
% 2.77/1.46  Index Insertion      : 0.00
% 2.77/1.46  Index Deletion       : 0.00
% 2.77/1.46  Index Matching       : 0.00
% 2.77/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
