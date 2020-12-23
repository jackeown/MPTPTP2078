%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:05 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 110 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 161 expanded)
%              Number of equality atoms :   31 (  63 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_354,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_70,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_36,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [D_27,A_22] : r2_hidden(D_27,k2_tarski(A_22,D_27)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [D_51,B_52,A_53] :
      ( ~ r2_hidden(D_51,B_52)
      | ~ r2_hidden(D_51,k4_xboole_0(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_180,plain,(
    ! [D_58,A_59] :
      ( ~ r2_hidden(D_58,A_59)
      | ~ r2_hidden(D_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_129])).

tff(c_190,plain,(
    ! [D_27] : ~ r2_hidden(D_27,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_74,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_193,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_300,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,k4_xboole_0(A_79,B_80))
      | r2_hidden(D_78,B_80)
      | ~ r2_hidden(D_78,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_315,plain,(
    ! [D_78] :
      ( r2_hidden(D_78,k1_xboole_0)
      | r2_hidden(D_78,'#skF_11')
      | ~ r2_hidden(D_78,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_300])).

tff(c_329,plain,(
    ! [D_81] :
      ( r2_hidden(D_81,'#skF_11')
      | ~ r2_hidden(D_81,k1_tarski('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_315])).

tff(c_337,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_329])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_337])).

tff(c_343,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_133,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_541,plain,(
    ! [A_112,B_113] :
      ( '#skF_1'(k1_tarski(A_112),B_113) = A_112
      | r1_tarski(k1_tarski(A_112),B_113) ) ),
    inference(resolution,[status(thm)],[c_133,c_34])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_624,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(k1_tarski(A_132),B_133) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_132),B_133) = A_132 ) ),
    inference(resolution,[status(thm)],[c_541,c_28])).

tff(c_673,plain,(
    '#skF_1'(k1_tarski('#skF_8'),'#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_354])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_736,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_4])).

tff(c_746,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_736])).

tff(c_757,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_746,c_28])).

tff(c_765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_757])).

tff(c_766,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_344,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),'#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_344])).

tff(c_797,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_xboole_0
    | ~ r2_hidden('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_809,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_68])).

tff(c_796,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_851,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_1'(A_156,B_157),A_156)
      | r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1121,plain,(
    ! [A_193,B_194] :
      ( '#skF_1'(k1_tarski(A_193),B_194) = A_193
      | r1_tarski(k1_tarski(A_193),B_194) ) ),
    inference(resolution,[status(thm)],[c_851,c_34])).

tff(c_1264,plain,(
    ! [A_222,B_223] :
      ( k4_xboole_0(k1_tarski(A_222),B_223) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_222),B_223) = A_222 ) ),
    inference(resolution,[status(thm)],[c_1121,c_28])).

tff(c_1322,plain,(
    '#skF_1'(k1_tarski('#skF_8'),'#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_809])).

tff(c_1334,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_4])).

tff(c_1344,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_1334])).

tff(c_1357,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1344,c_28])).

tff(c_1366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_809,c_1357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:52:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.46  
% 3.19/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.47  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.19/1.47  
% 3.19/1.47  %Foreground sorts:
% 3.19/1.47  
% 3.19/1.47  
% 3.19/1.47  %Background operators:
% 3.19/1.47  
% 3.19/1.47  
% 3.19/1.47  %Foreground operators:
% 3.19/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.47  tff('#skF_11', type, '#skF_11': $i).
% 3.19/1.47  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.19/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.47  tff('#skF_10', type, '#skF_10': $i).
% 3.19/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.19/1.47  tff('#skF_9', type, '#skF_9': $i).
% 3.19/1.47  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.19/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.19/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.19/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.19/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.19/1.47  
% 3.19/1.48  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 3.19/1.48  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.19/1.48  tff(f_66, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.19/1.48  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.19/1.48  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.19/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.48  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.19/1.48  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.19/1.48  tff(c_354, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 3.19/1.48  tff(c_70, plain, (r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.19/1.48  tff(c_108, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_70])).
% 3.19/1.48  tff(c_36, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.48  tff(c_48, plain, (![D_27, A_22]: (r2_hidden(D_27, k2_tarski(A_22, D_27)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.19/1.48  tff(c_32, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.19/1.48  tff(c_129, plain, (![D_51, B_52, A_53]: (~r2_hidden(D_51, B_52) | ~r2_hidden(D_51, k4_xboole_0(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.19/1.48  tff(c_180, plain, (![D_58, A_59]: (~r2_hidden(D_58, A_59) | ~r2_hidden(D_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_129])).
% 3.19/1.48  tff(c_190, plain, (![D_27]: (~r2_hidden(D_27, k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_180])).
% 3.19/1.48  tff(c_74, plain, (r2_hidden('#skF_8', '#skF_9') | k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.19/1.48  tff(c_193, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 3.19/1.48  tff(c_300, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, k4_xboole_0(A_79, B_80)) | r2_hidden(D_78, B_80) | ~r2_hidden(D_78, A_79))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.19/1.48  tff(c_315, plain, (![D_78]: (r2_hidden(D_78, k1_xboole_0) | r2_hidden(D_78, '#skF_11') | ~r2_hidden(D_78, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_193, c_300])).
% 3.19/1.48  tff(c_329, plain, (![D_81]: (r2_hidden(D_81, '#skF_11') | ~r2_hidden(D_81, k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_190, c_315])).
% 3.19/1.48  tff(c_337, plain, (r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_36, c_329])).
% 3.19/1.48  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_337])).
% 3.19/1.48  tff(c_343, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_74])).
% 3.19/1.48  tff(c_133, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.48  tff(c_34, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.48  tff(c_541, plain, (![A_112, B_113]: ('#skF_1'(k1_tarski(A_112), B_113)=A_112 | r1_tarski(k1_tarski(A_112), B_113))), inference(resolution, [status(thm)], [c_133, c_34])).
% 3.19/1.48  tff(c_28, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.48  tff(c_624, plain, (![A_132, B_133]: (k4_xboole_0(k1_tarski(A_132), B_133)=k1_xboole_0 | '#skF_1'(k1_tarski(A_132), B_133)=A_132)), inference(resolution, [status(thm)], [c_541, c_28])).
% 3.19/1.48  tff(c_673, plain, ('#skF_1'(k1_tarski('#skF_8'), '#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_624, c_354])).
% 3.19/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.48  tff(c_736, plain, (~r2_hidden('#skF_8', '#skF_9') | r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_673, c_4])).
% 3.19/1.48  tff(c_746, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_736])).
% 3.19/1.48  tff(c_757, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_746, c_28])).
% 3.19/1.48  tff(c_765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_757])).
% 3.19/1.48  tff(c_766, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 3.19/1.48  tff(c_344, plain, (k4_xboole_0(k1_tarski('#skF_10'), '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 3.19/1.48  tff(c_795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_766, c_344])).
% 3.19/1.48  tff(c_797, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_70])).
% 3.19/1.48  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_xboole_0 | ~r2_hidden('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.19/1.48  tff(c_809, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_797, c_68])).
% 3.19/1.48  tff(c_796, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 3.19/1.48  tff(c_851, plain, (![A_156, B_157]: (r2_hidden('#skF_1'(A_156, B_157), A_156) | r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.48  tff(c_1121, plain, (![A_193, B_194]: ('#skF_1'(k1_tarski(A_193), B_194)=A_193 | r1_tarski(k1_tarski(A_193), B_194))), inference(resolution, [status(thm)], [c_851, c_34])).
% 3.19/1.48  tff(c_1264, plain, (![A_222, B_223]: (k4_xboole_0(k1_tarski(A_222), B_223)=k1_xboole_0 | '#skF_1'(k1_tarski(A_222), B_223)=A_222)), inference(resolution, [status(thm)], [c_1121, c_28])).
% 3.19/1.48  tff(c_1322, plain, ('#skF_1'(k1_tarski('#skF_8'), '#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1264, c_809])).
% 3.19/1.48  tff(c_1334, plain, (~r2_hidden('#skF_8', '#skF_9') | r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1322, c_4])).
% 3.19/1.48  tff(c_1344, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_1334])).
% 3.19/1.48  tff(c_1357, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_1344, c_28])).
% 3.19/1.48  tff(c_1366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_809, c_1357])).
% 3.19/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  Inference rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Ref     : 0
% 3.19/1.48  #Sup     : 302
% 3.19/1.48  #Fact    : 0
% 3.19/1.48  #Define  : 0
% 3.19/1.48  #Split   : 3
% 3.19/1.48  #Chain   : 0
% 3.19/1.48  #Close   : 0
% 3.19/1.48  
% 3.19/1.48  Ordering : KBO
% 3.19/1.48  
% 3.19/1.48  Simplification rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Subsume      : 99
% 3.19/1.48  #Demod        : 40
% 3.19/1.48  #Tautology    : 106
% 3.19/1.48  #SimpNegUnit  : 20
% 3.19/1.48  #BackRed      : 0
% 3.19/1.48  
% 3.19/1.48  #Partial instantiations: 0
% 3.19/1.48  #Strategies tried      : 1
% 3.19/1.48  
% 3.19/1.48  Timing (in seconds)
% 3.19/1.48  ----------------------
% 3.19/1.48  Preprocessing        : 0.32
% 3.19/1.48  Parsing              : 0.16
% 3.19/1.48  CNF conversion       : 0.03
% 3.19/1.48  Main loop            : 0.41
% 3.19/1.48  Inferencing          : 0.15
% 3.19/1.48  Reduction            : 0.12
% 3.19/1.48  Demodulation         : 0.08
% 3.19/1.48  BG Simplification    : 0.02
% 3.19/1.48  Subsumption          : 0.08
% 3.19/1.48  Abstraction          : 0.02
% 3.19/1.48  MUC search           : 0.00
% 3.19/1.48  Cooper               : 0.00
% 3.19/1.48  Total                : 0.75
% 3.19/1.48  Index Insertion      : 0.00
% 3.19/1.48  Index Deletion       : 0.00
% 3.19/1.48  Index Matching       : 0.00
% 3.19/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
