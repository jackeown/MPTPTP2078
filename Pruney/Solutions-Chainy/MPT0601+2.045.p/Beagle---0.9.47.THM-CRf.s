%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 134 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [C_25,A_10] :
      ( r2_hidden(k4_tarski(C_25,'#skF_7'(A_10,k1_relat_1(A_10),C_25)),A_10)
      | ~ r2_hidden(C_25,k1_relat_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_636,plain,(
    ! [C_107,A_108] :
      ( r2_hidden(k4_tarski(C_107,'#skF_7'(A_108,k1_relat_1(A_108),C_107)),A_108)
      | ~ r2_hidden(C_107,k1_relat_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_313,plain,(
    ! [D_68,B_69,A_70] :
      ( ~ r2_hidden(D_68,B_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_320,plain,(
    ! [D_68,A_9] :
      ( ~ r2_hidden(D_68,k1_xboole_0)
      | ~ r2_hidden(D_68,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_313])).

tff(c_746,plain,(
    ! [C_117,A_118] :
      ( ~ r2_hidden(k4_tarski(C_117,'#skF_7'(k1_xboole_0,k1_relat_1(k1_xboole_0),C_117)),A_118)
      | ~ r2_hidden(C_117,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_636,c_320])).

tff(c_777,plain,(
    ! [C_119] : ~ r2_hidden(C_119,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_24,c_746])).

tff(c_817,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_777])).

tff(c_772,plain,(
    ! [C_25] : ~ r2_hidden(C_25,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_24,c_746])).

tff(c_818,plain,(
    ! [C_25] : ~ r2_hidden(C_25,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_772])).

tff(c_42,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_48])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_237,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden(k4_tarski(A_57,B_58),C_59)
      | ~ r2_hidden(B_58,k11_relat_1(C_59,A_57))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [C_25,A_10,D_28] :
      ( r2_hidden(C_25,k1_relat_1(A_10))
      | ~ r2_hidden(k4_tarski(C_25,D_28),A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_270,plain,(
    ! [A_63,C_64,B_65] :
      ( r2_hidden(A_63,k1_relat_1(C_64))
      | ~ r2_hidden(B_65,k11_relat_1(C_64,A_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_283,plain,(
    ! [A_66,C_67] :
      ( r2_hidden(A_66,k1_relat_1(C_67))
      | ~ v1_relat_1(C_67)
      | k11_relat_1(C_67,A_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_270])).

tff(c_298,plain,
    ( ~ v1_relat_1('#skF_9')
    | k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_283,c_59])).

tff(c_304,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_298])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_304])).

tff(c_308,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_307,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,(
    ! [B_30,C_31,A_29] :
      ( r2_hidden(B_30,k11_relat_1(C_31,A_29))
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2359,plain,(
    ! [A_195,C_196] :
      ( r2_hidden('#skF_7'(A_195,k1_relat_1(A_195),C_196),k11_relat_1(A_195,C_196))
      | ~ v1_relat_1(A_195)
      | ~ r2_hidden(C_196,k1_relat_1(A_195)) ) ),
    inference(resolution,[status(thm)],[c_636,c_38])).

tff(c_2373,plain,
    ( r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0)
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_2359])).

tff(c_2378,plain,(
    r2_hidden('#skF_7'('#skF_9',k1_relat_1('#skF_9'),'#skF_8'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_40,c_2373])).

tff(c_2380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_818,c_2378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.62  
% 3.45/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.62  %$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.75/1.62  
% 3.75/1.62  %Foreground sorts:
% 3.75/1.62  
% 3.75/1.62  
% 3.75/1.62  %Background operators:
% 3.75/1.62  
% 3.75/1.62  
% 3.75/1.62  %Foreground operators:
% 3.75/1.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.75/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.75/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.75/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.75/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.75/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.75/1.62  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.75/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.75/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.62  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.75/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.75/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.75/1.62  
% 3.75/1.63  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.75/1.63  tff(f_53, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.75/1.63  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.75/1.63  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.75/1.63  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.75/1.63  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.75/1.63  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.75/1.63  tff(c_24, plain, (![C_25, A_10]: (r2_hidden(k4_tarski(C_25, '#skF_7'(A_10, k1_relat_1(A_10), C_25)), A_10) | ~r2_hidden(C_25, k1_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.63  tff(c_636, plain, (![C_107, A_108]: (r2_hidden(k4_tarski(C_107, '#skF_7'(A_108, k1_relat_1(A_108), C_107)), A_108) | ~r2_hidden(C_107, k1_relat_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.63  tff(c_22, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.75/1.63  tff(c_313, plain, (![D_68, B_69, A_70]: (~r2_hidden(D_68, B_69) | ~r2_hidden(D_68, k4_xboole_0(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.63  tff(c_320, plain, (![D_68, A_9]: (~r2_hidden(D_68, k1_xboole_0) | ~r2_hidden(D_68, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_313])).
% 3.75/1.63  tff(c_746, plain, (![C_117, A_118]: (~r2_hidden(k4_tarski(C_117, '#skF_7'(k1_xboole_0, k1_relat_1(k1_xboole_0), C_117)), A_118) | ~r2_hidden(C_117, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_636, c_320])).
% 3.75/1.63  tff(c_777, plain, (![C_119]: (~r2_hidden(C_119, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_24, c_746])).
% 3.75/1.63  tff(c_817, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_777])).
% 3.75/1.63  tff(c_772, plain, (![C_25]: (~r2_hidden(C_25, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_24, c_746])).
% 3.75/1.63  tff(c_818, plain, (![C_25]: (~r2_hidden(C_25, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_772])).
% 3.75/1.63  tff(c_42, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.75/1.63  tff(c_59, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.75/1.63  tff(c_48, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9')) | k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.75/1.63  tff(c_69, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_59, c_48])).
% 3.75/1.63  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.75/1.63  tff(c_237, plain, (![A_57, B_58, C_59]: (r2_hidden(k4_tarski(A_57, B_58), C_59) | ~r2_hidden(B_58, k11_relat_1(C_59, A_57)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.75/1.63  tff(c_26, plain, (![C_25, A_10, D_28]: (r2_hidden(C_25, k1_relat_1(A_10)) | ~r2_hidden(k4_tarski(C_25, D_28), A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.63  tff(c_270, plain, (![A_63, C_64, B_65]: (r2_hidden(A_63, k1_relat_1(C_64)) | ~r2_hidden(B_65, k11_relat_1(C_64, A_63)) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_237, c_26])).
% 3.75/1.63  tff(c_283, plain, (![A_66, C_67]: (r2_hidden(A_66, k1_relat_1(C_67)) | ~v1_relat_1(C_67) | k11_relat_1(C_67, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_270])).
% 3.75/1.63  tff(c_298, plain, (~v1_relat_1('#skF_9') | k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_283, c_59])).
% 3.75/1.63  tff(c_304, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_298])).
% 3.75/1.63  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_304])).
% 3.75/1.63  tff(c_308, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_42])).
% 3.75/1.63  tff(c_307, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.75/1.63  tff(c_38, plain, (![B_30, C_31, A_29]: (r2_hidden(B_30, k11_relat_1(C_31, A_29)) | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.75/1.63  tff(c_2359, plain, (![A_195, C_196]: (r2_hidden('#skF_7'(A_195, k1_relat_1(A_195), C_196), k11_relat_1(A_195, C_196)) | ~v1_relat_1(A_195) | ~r2_hidden(C_196, k1_relat_1(A_195)))), inference(resolution, [status(thm)], [c_636, c_38])).
% 3.75/1.63  tff(c_2373, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0) | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_2359])).
% 3.75/1.63  tff(c_2378, plain, (r2_hidden('#skF_7'('#skF_9', k1_relat_1('#skF_9'), '#skF_8'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_308, c_40, c_2373])).
% 3.75/1.63  tff(c_2380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_818, c_2378])).
% 3.75/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.63  
% 3.75/1.63  Inference rules
% 3.75/1.63  ----------------------
% 3.75/1.63  #Ref     : 0
% 3.75/1.63  #Sup     : 517
% 3.75/1.63  #Fact    : 0
% 3.75/1.63  #Define  : 0
% 3.75/1.63  #Split   : 2
% 3.75/1.63  #Chain   : 0
% 3.75/1.63  #Close   : 0
% 3.75/1.63  
% 3.75/1.63  Ordering : KBO
% 3.75/1.63  
% 3.75/1.63  Simplification rules
% 3.75/1.63  ----------------------
% 3.75/1.63  #Subsume      : 136
% 3.75/1.63  #Demod        : 171
% 3.75/1.63  #Tautology    : 159
% 3.75/1.63  #SimpNegUnit  : 23
% 3.75/1.63  #BackRed      : 1
% 3.75/1.63  
% 3.75/1.63  #Partial instantiations: 0
% 3.75/1.63  #Strategies tried      : 1
% 3.75/1.63  
% 3.75/1.63  Timing (in seconds)
% 3.75/1.63  ----------------------
% 3.75/1.63  Preprocessing        : 0.28
% 3.75/1.63  Parsing              : 0.15
% 3.75/1.64  CNF conversion       : 0.02
% 3.75/1.64  Main loop            : 0.59
% 3.75/1.64  Inferencing          : 0.22
% 3.75/1.64  Reduction            : 0.16
% 3.75/1.64  Demodulation         : 0.10
% 3.75/1.64  BG Simplification    : 0.03
% 3.75/1.64  Subsumption          : 0.14
% 3.75/1.64  Abstraction          : 0.03
% 3.75/1.64  MUC search           : 0.00
% 3.75/1.64  Cooper               : 0.00
% 3.75/1.64  Total                : 0.90
% 3.75/1.64  Index Insertion      : 0.00
% 3.75/1.64  Index Deletion       : 0.00
% 3.75/1.64  Index Matching       : 0.00
% 3.75/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
