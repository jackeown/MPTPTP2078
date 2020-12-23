%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 108 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 188 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_225,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_72)
      | r2_hidden('#skF_2'(A_71,B_72),A_71)
      | B_72 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_233,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | r2_hidden('#skF_1'(A_71,B_72),B_72)
      | B_72 = A_71 ) ),
    inference(resolution,[status(thm)],[c_225,c_12])).

tff(c_339,plain,(
    ! [C_98,A_99] :
      ( r2_hidden(k4_tarski(C_98,'#skF_6'(A_99,k1_relat_1(A_99),C_98)),A_99)
      | ~ r2_hidden(C_98,k1_relat_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_357,plain,(
    ! [A_100,C_101] :
      ( ~ v1_xboole_0(A_100)
      | ~ r2_hidden(C_101,k1_relat_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_339,c_12])).

tff(c_434,plain,(
    ! [A_106,A_107] :
      ( ~ v1_xboole_0(A_106)
      | ~ v1_xboole_0(A_107)
      | k1_relat_1(A_106) = A_107 ) ),
    inference(resolution,[status(thm)],[c_233,c_357])).

tff(c_438,plain,(
    ! [A_108] :
      ( ~ v1_xboole_0(A_108)
      | k1_relat_1(k1_xboole_0) = A_108 ) ),
    inference(resolution,[status(thm)],[c_2,c_434])).

tff(c_442,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_438])).

tff(c_14,plain,(
    ! [C_21,A_6] :
      ( r2_hidden(k4_tarski(C_21,'#skF_6'(A_6,k1_relat_1(A_6),C_21)),A_6)
      | ~ r2_hidden(C_21,k1_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_389,plain,(
    ! [A_100,C_21] :
      ( ~ v1_xboole_0(A_100)
      | ~ r2_hidden(C_21,k1_relat_1(k1_relat_1(A_100))) ) ),
    inference(resolution,[status(thm)],[c_14,c_357])).

tff(c_447,plain,(
    ! [C_21] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_21,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_389])).

tff(c_457,plain,(
    ! [C_21] : ~ r2_hidden(C_21,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_2,c_447])).

tff(c_32,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_41,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38])).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r2_hidden('#skF_2'(A_46,B_47),A_46)
      | B_47 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | r2_hidden('#skF_2'(A_49,B_48),A_49)
      | B_48 = A_49 ) ),
    inference(resolution,[status(thm)],[c_65,c_12])).

tff(c_43,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [A_33,C_35,B_34] :
      ( r2_hidden(A_33,k1_relat_1(C_35))
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_43,c_16])).

tff(c_177,plain,(
    ! [A_63,C_64,B_65] :
      ( r2_hidden(A_63,k1_relat_1(C_64))
      | ~ v1_relat_1(C_64)
      | ~ v1_xboole_0(B_65)
      | k11_relat_1(C_64,A_63) = B_65 ) ),
    inference(resolution,[status(thm)],[c_99,c_50])).

tff(c_181,plain,(
    ! [A_66,C_67] :
      ( r2_hidden(A_66,k1_relat_1(C_67))
      | ~ v1_relat_1(C_67)
      | k11_relat_1(C_67,A_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_177])).

tff(c_199,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181,c_40])).

tff(c_209,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_199])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_209])).

tff(c_213,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_212,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,(
    ! [B_26,C_27,A_25] :
      ( r2_hidden(B_26,k11_relat_1(C_27,A_25))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2096,plain,(
    ! [A_179,C_180] :
      ( r2_hidden('#skF_6'(A_179,k1_relat_1(A_179),C_180),k11_relat_1(A_179,C_180))
      | ~ v1_relat_1(A_179)
      | ~ r2_hidden(C_180,k1_relat_1(A_179)) ) ),
    inference(resolution,[status(thm)],[c_339,c_28])).

tff(c_2129,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2096])).

tff(c_2136,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_30,c_2129])).

tff(c_2138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_2136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:23:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.59  
% 3.41/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.59  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.41/1.59  
% 3.41/1.59  %Foreground sorts:
% 3.41/1.59  
% 3.41/1.59  
% 3.41/1.59  %Background operators:
% 3.41/1.59  
% 3.41/1.59  
% 3.41/1.59  %Foreground operators:
% 3.41/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.41/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.41/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.41/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.41/1.59  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.41/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.41/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.41/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.41/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.41/1.59  
% 3.41/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.41/1.60  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.41/1.60  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 3.41/1.60  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.41/1.60  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.41/1.60  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.41/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.41/1.60  tff(c_225, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), B_72) | r2_hidden('#skF_2'(A_71, B_72), A_71) | B_72=A_71)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.41/1.60  tff(c_12, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.60  tff(c_233, plain, (![A_71, B_72]: (~v1_xboole_0(A_71) | r2_hidden('#skF_1'(A_71, B_72), B_72) | B_72=A_71)), inference(resolution, [status(thm)], [c_225, c_12])).
% 3.41/1.60  tff(c_339, plain, (![C_98, A_99]: (r2_hidden(k4_tarski(C_98, '#skF_6'(A_99, k1_relat_1(A_99), C_98)), A_99) | ~r2_hidden(C_98, k1_relat_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.60  tff(c_357, plain, (![A_100, C_101]: (~v1_xboole_0(A_100) | ~r2_hidden(C_101, k1_relat_1(A_100)))), inference(resolution, [status(thm)], [c_339, c_12])).
% 3.41/1.60  tff(c_434, plain, (![A_106, A_107]: (~v1_xboole_0(A_106) | ~v1_xboole_0(A_107) | k1_relat_1(A_106)=A_107)), inference(resolution, [status(thm)], [c_233, c_357])).
% 3.41/1.60  tff(c_438, plain, (![A_108]: (~v1_xboole_0(A_108) | k1_relat_1(k1_xboole_0)=A_108)), inference(resolution, [status(thm)], [c_2, c_434])).
% 3.41/1.60  tff(c_442, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_438])).
% 3.41/1.60  tff(c_14, plain, (![C_21, A_6]: (r2_hidden(k4_tarski(C_21, '#skF_6'(A_6, k1_relat_1(A_6), C_21)), A_6) | ~r2_hidden(C_21, k1_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.60  tff(c_389, plain, (![A_100, C_21]: (~v1_xboole_0(A_100) | ~r2_hidden(C_21, k1_relat_1(k1_relat_1(A_100))))), inference(resolution, [status(thm)], [c_14, c_357])).
% 3.41/1.60  tff(c_447, plain, (![C_21]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_21, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_442, c_389])).
% 3.41/1.60  tff(c_457, plain, (![C_21]: (~r2_hidden(C_21, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_2, c_447])).
% 3.41/1.60  tff(c_32, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.41/1.60  tff(c_40, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.41/1.60  tff(c_38, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.41/1.60  tff(c_41, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_38])).
% 3.41/1.60  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.41/1.60  tff(c_65, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), B_47) | r2_hidden('#skF_2'(A_46, B_47), A_46) | B_47=A_46)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.41/1.60  tff(c_99, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | r2_hidden('#skF_2'(A_49, B_48), A_49) | B_48=A_49)), inference(resolution, [status(thm)], [c_65, c_12])).
% 3.41/1.60  tff(c_43, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.41/1.60  tff(c_16, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.60  tff(c_50, plain, (![A_33, C_35, B_34]: (r2_hidden(A_33, k1_relat_1(C_35)) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_43, c_16])).
% 3.41/1.60  tff(c_177, plain, (![A_63, C_64, B_65]: (r2_hidden(A_63, k1_relat_1(C_64)) | ~v1_relat_1(C_64) | ~v1_xboole_0(B_65) | k11_relat_1(C_64, A_63)=B_65)), inference(resolution, [status(thm)], [c_99, c_50])).
% 3.41/1.60  tff(c_181, plain, (![A_66, C_67]: (r2_hidden(A_66, k1_relat_1(C_67)) | ~v1_relat_1(C_67) | k11_relat_1(C_67, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_177])).
% 3.41/1.60  tff(c_199, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_181, c_40])).
% 3.41/1.60  tff(c_209, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_199])).
% 3.41/1.60  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_209])).
% 3.41/1.60  tff(c_213, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_32])).
% 3.41/1.60  tff(c_212, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.41/1.60  tff(c_28, plain, (![B_26, C_27, A_25]: (r2_hidden(B_26, k11_relat_1(C_27, A_25)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.41/1.60  tff(c_2096, plain, (![A_179, C_180]: (r2_hidden('#skF_6'(A_179, k1_relat_1(A_179), C_180), k11_relat_1(A_179, C_180)) | ~v1_relat_1(A_179) | ~r2_hidden(C_180, k1_relat_1(A_179)))), inference(resolution, [status(thm)], [c_339, c_28])).
% 3.41/1.60  tff(c_2129, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_2096])).
% 3.41/1.60  tff(c_2136, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_30, c_2129])).
% 3.41/1.60  tff(c_2138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_2136])).
% 3.41/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.60  
% 3.41/1.60  Inference rules
% 3.41/1.60  ----------------------
% 3.41/1.60  #Ref     : 0
% 3.41/1.60  #Sup     : 470
% 3.41/1.60  #Fact    : 0
% 3.41/1.60  #Define  : 0
% 3.41/1.60  #Split   : 4
% 3.41/1.60  #Chain   : 0
% 3.41/1.60  #Close   : 0
% 3.41/1.60  
% 3.41/1.60  Ordering : KBO
% 3.41/1.60  
% 3.41/1.60  Simplification rules
% 3.41/1.60  ----------------------
% 3.41/1.60  #Subsume      : 178
% 3.41/1.60  #Demod        : 264
% 3.41/1.60  #Tautology    : 107
% 3.41/1.60  #SimpNegUnit  : 22
% 3.41/1.60  #BackRed      : 1
% 3.41/1.60  
% 3.41/1.60  #Partial instantiations: 0
% 3.41/1.60  #Strategies tried      : 1
% 3.41/1.60  
% 3.41/1.60  Timing (in seconds)
% 3.41/1.60  ----------------------
% 3.41/1.61  Preprocessing        : 0.28
% 3.41/1.61  Parsing              : 0.16
% 3.41/1.61  CNF conversion       : 0.02
% 3.41/1.61  Main loop            : 0.55
% 3.41/1.61  Inferencing          : 0.21
% 3.41/1.61  Reduction            : 0.13
% 3.41/1.61  Demodulation         : 0.08
% 3.41/1.61  BG Simplification    : 0.03
% 3.41/1.61  Subsumption          : 0.15
% 3.41/1.61  Abstraction          : 0.03
% 3.41/1.61  MUC search           : 0.00
% 3.41/1.61  Cooper               : 0.00
% 3.41/1.61  Total                : 0.86
% 3.41/1.61  Index Insertion      : 0.00
% 3.41/1.61  Index Deletion       : 0.00
% 3.41/1.61  Index Matching       : 0.00
% 3.41/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
