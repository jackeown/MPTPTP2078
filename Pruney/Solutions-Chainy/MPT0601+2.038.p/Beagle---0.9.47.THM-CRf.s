%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 112 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2119,plain,(
    ! [C_124,A_125] :
      ( r2_hidden(k4_tarski(C_124,'#skF_5'(A_125,k1_relat_1(A_125),C_124)),A_125)
      | ~ r2_hidden(C_124,k1_relat_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2141,plain,(
    ! [A_126,C_127] :
      ( ~ v1_xboole_0(A_126)
      | ~ r2_hidden(C_127,k1_relat_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_2119,c_2])).

tff(c_2159,plain,(
    ! [C_127] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_127,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2141])).

tff(c_2165,plain,(
    ! [C_127] : ~ r2_hidden(C_127,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2159])).

tff(c_32,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_38])).

tff(c_30,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden(k4_tarski(A_38,B_39),C_40)
      | ~ r2_hidden(B_39,k11_relat_1(C_40,A_38))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1923,plain,(
    ! [A_105,C_106,B_107] :
      ( r2_hidden(A_105,k1_relat_1(C_106))
      | ~ r2_hidden(B_107,k11_relat_1(C_106,A_105))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_63,c_12])).

tff(c_1948,plain,(
    ! [A_108,C_109] :
      ( r2_hidden(A_108,k1_relat_1(C_109))
      | ~ v1_relat_1(C_109)
      | v1_xboole_0(k11_relat_1(C_109,A_108)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1923])).

tff(c_1992,plain,
    ( ~ v1_relat_1('#skF_7')
    | v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1948,c_59])).

tff(c_2033,plain,(
    v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1992])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2060,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2033,c_8])).

tff(c_2072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2060])).

tff(c_2073,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2080,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2073,c_38])).

tff(c_24,plain,(
    ! [B_26,C_27,A_25] :
      ( r2_hidden(B_26,k11_relat_1(C_27,A_25))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5508,plain,(
    ! [A_225,C_226] :
      ( r2_hidden('#skF_5'(A_225,k1_relat_1(A_225),C_226),k11_relat_1(A_225,C_226))
      | ~ v1_relat_1(A_225)
      | ~ r2_hidden(C_226,k1_relat_1(A_225)) ) ),
    inference(resolution,[status(thm)],[c_2119,c_24])).

tff(c_5550,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2073,c_5508])).

tff(c_5559,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_30,c_5550])).

tff(c_5561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2165,c_5559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.14  
% 5.14/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.14  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 5.14/2.14  
% 5.14/2.14  %Foreground sorts:
% 5.14/2.14  
% 5.14/2.14  
% 5.14/2.14  %Background operators:
% 5.14/2.14  
% 5.14/2.14  
% 5.14/2.14  %Foreground operators:
% 5.14/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.14/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.14/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/2.14  tff('#skF_7', type, '#skF_7': $i).
% 5.14/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.14/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.14/2.14  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.14/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.14/2.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.14/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.14/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.14/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.14/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.14/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.14/2.14  
% 5.14/2.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.14/2.15  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.14/2.15  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.14/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.14/2.15  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 5.14/2.15  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 5.14/2.15  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.14/2.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.14/2.15  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.14/2.15  tff(c_2119, plain, (![C_124, A_125]: (r2_hidden(k4_tarski(C_124, '#skF_5'(A_125, k1_relat_1(A_125), C_124)), A_125) | ~r2_hidden(C_124, k1_relat_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.14/2.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.15  tff(c_2141, plain, (![A_126, C_127]: (~v1_xboole_0(A_126) | ~r2_hidden(C_127, k1_relat_1(A_126)))), inference(resolution, [status(thm)], [c_2119, c_2])).
% 5.14/2.15  tff(c_2159, plain, (![C_127]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_127, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2141])).
% 5.14/2.15  tff(c_2165, plain, (![C_127]: (~r2_hidden(C_127, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2159])).
% 5.14/2.15  tff(c_32, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.14/2.15  tff(c_59, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_32])).
% 5.14/2.15  tff(c_38, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.14/2.15  tff(c_60, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_59, c_38])).
% 5.14/2.15  tff(c_30, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.14/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.15  tff(c_63, plain, (![A_38, B_39, C_40]: (r2_hidden(k4_tarski(A_38, B_39), C_40) | ~r2_hidden(B_39, k11_relat_1(C_40, A_38)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.14/2.15  tff(c_12, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.14/2.15  tff(c_1923, plain, (![A_105, C_106, B_107]: (r2_hidden(A_105, k1_relat_1(C_106)) | ~r2_hidden(B_107, k11_relat_1(C_106, A_105)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_63, c_12])).
% 5.14/2.15  tff(c_1948, plain, (![A_108, C_109]: (r2_hidden(A_108, k1_relat_1(C_109)) | ~v1_relat_1(C_109) | v1_xboole_0(k11_relat_1(C_109, A_108)))), inference(resolution, [status(thm)], [c_4, c_1923])).
% 5.14/2.15  tff(c_1992, plain, (~v1_relat_1('#skF_7') | v1_xboole_0(k11_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_1948, c_59])).
% 5.14/2.15  tff(c_2033, plain, (v1_xboole_0(k11_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1992])).
% 5.14/2.15  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.14/2.15  tff(c_2060, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2033, c_8])).
% 5.14/2.15  tff(c_2072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2060])).
% 5.14/2.15  tff(c_2073, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 5.14/2.15  tff(c_2080, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2073, c_38])).
% 5.14/2.15  tff(c_24, plain, (![B_26, C_27, A_25]: (r2_hidden(B_26, k11_relat_1(C_27, A_25)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.14/2.15  tff(c_5508, plain, (![A_225, C_226]: (r2_hidden('#skF_5'(A_225, k1_relat_1(A_225), C_226), k11_relat_1(A_225, C_226)) | ~v1_relat_1(A_225) | ~r2_hidden(C_226, k1_relat_1(A_225)))), inference(resolution, [status(thm)], [c_2119, c_24])).
% 5.14/2.15  tff(c_5550, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2073, c_5508])).
% 5.14/2.15  tff(c_5559, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_30, c_5550])).
% 5.14/2.15  tff(c_5561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2165, c_5559])).
% 5.14/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.15  
% 5.14/2.15  Inference rules
% 5.14/2.15  ----------------------
% 5.14/2.15  #Ref     : 0
% 5.14/2.15  #Sup     : 1441
% 5.14/2.15  #Fact    : 0
% 5.14/2.15  #Define  : 0
% 5.14/2.15  #Split   : 4
% 5.14/2.15  #Chain   : 0
% 5.14/2.15  #Close   : 0
% 5.14/2.15  
% 5.14/2.15  Ordering : KBO
% 5.14/2.15  
% 5.14/2.15  Simplification rules
% 5.14/2.15  ----------------------
% 5.14/2.15  #Subsume      : 529
% 5.14/2.15  #Demod        : 1161
% 5.14/2.15  #Tautology    : 416
% 5.14/2.15  #SimpNegUnit  : 43
% 5.14/2.15  #BackRed      : 0
% 5.14/2.15  
% 5.14/2.15  #Partial instantiations: 0
% 5.14/2.15  #Strategies tried      : 1
% 5.14/2.15  
% 5.14/2.15  Timing (in seconds)
% 5.14/2.15  ----------------------
% 5.14/2.15  Preprocessing        : 0.30
% 5.14/2.15  Parsing              : 0.16
% 5.14/2.15  CNF conversion       : 0.02
% 5.14/2.15  Main loop            : 0.91
% 5.14/2.15  Inferencing          : 0.29
% 5.14/2.15  Reduction            : 0.24
% 5.14/2.15  Demodulation         : 0.17
% 5.14/2.15  BG Simplification    : 0.04
% 5.14/2.15  Subsumption          : 0.29
% 5.14/2.15  Abstraction          : 0.06
% 5.14/2.15  MUC search           : 0.00
% 5.14/2.15  Cooper               : 0.00
% 5.14/2.15  Total                : 1.25
% 5.14/2.15  Index Insertion      : 0.00
% 5.14/2.15  Index Deletion       : 0.00
% 5.14/2.15  Index Matching       : 0.00
% 5.14/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
