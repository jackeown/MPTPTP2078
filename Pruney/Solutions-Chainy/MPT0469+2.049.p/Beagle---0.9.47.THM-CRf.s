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
% DateTime   : Thu Dec  3 09:58:58 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   55 (  81 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 100 expanded)
%              Number of equality atoms :   17 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_10,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [C_22,A_7] :
      ( r2_hidden(k4_tarski(C_22,'#skF_6'(A_7,k1_relat_1(A_7),C_22)),A_7)
      | ~ r2_hidden(C_22,k1_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_63,plain,(
    ! [A_58,C_59] :
      ( r2_hidden(k4_tarski('#skF_10'(A_58,k2_relat_1(A_58),C_59),C_59),A_58)
      | ~ r2_hidden(C_59,k2_relat_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_60,C_61] :
      ( ~ v1_xboole_0(A_60)
      | ~ r2_hidden(C_61,k2_relat_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_92,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(A_62)
      | k2_relat_1(A_62) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_96,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_92])).

tff(c_75,plain,(
    ! [A_58,C_59] :
      ( ~ v1_xboole_0(A_58)
      | ~ r2_hidden(C_59,k2_relat_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_100,plain,(
    ! [C_59] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_75])).

tff(c_128,plain,(
    ! [C_65] : ~ r2_hidden(C_65,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_100])).

tff(c_152,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_12,c_128])).

tff(c_164,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_164])).

tff(c_175,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_430,plain,(
    ! [A_89,C_90] :
      ( r2_hidden(k4_tarski('#skF_10'(A_89,k2_relat_1(A_89),C_90),C_90),A_89)
      | ~ r2_hidden(C_90,k2_relat_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_176,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_195,plain,(
    ! [C_77,A_78] :
      ( r2_hidden(k4_tarski(C_77,'#skF_6'(A_78,k1_relat_1(A_78),C_77)),A_78)
      | ~ r2_hidden(C_77,k1_relat_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_212,plain,(
    ! [A_79,C_80] :
      ( ~ v1_xboole_0(A_79)
      | ~ r2_hidden(C_80,k1_relat_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_223,plain,(
    ! [C_80] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_212])).

tff(c_231,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_223])).

tff(c_458,plain,(
    ! [C_91] : ~ r2_hidden(C_91,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_430,c_231])).

tff(c_470,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_458])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_470])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.23  
% 1.86/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.23  %$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4 > #skF_10
% 1.86/1.23  
% 1.86/1.23  %Foreground sorts:
% 1.86/1.23  
% 1.86/1.23  
% 1.86/1.23  %Background operators:
% 1.86/1.23  
% 1.86/1.23  
% 1.86/1.23  %Foreground operators:
% 1.86/1.23  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.86/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.23  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.86/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.86/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.86/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.23  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.23  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.86/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.23  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 1.86/1.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.86/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.86/1.23  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 1.86/1.23  
% 2.07/1.24  tff(f_61, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.07/1.24  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.24  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.07/1.24  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 2.07/1.24  tff(f_33, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.07/1.24  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.07/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.24  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.24  tff(c_48, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.07/1.24  tff(c_10, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.24  tff(c_12, plain, (![C_22, A_7]: (r2_hidden(k4_tarski(C_22, '#skF_6'(A_7, k1_relat_1(A_7), C_22)), A_7) | ~r2_hidden(C_22, k1_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.07/1.24  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.24  tff(c_8, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.24  tff(c_37, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.07/1.24  tff(c_63, plain, (![A_58, C_59]: (r2_hidden(k4_tarski('#skF_10'(A_58, k2_relat_1(A_58), C_59), C_59), A_58) | ~r2_hidden(C_59, k2_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.24  tff(c_76, plain, (![A_60, C_61]: (~v1_xboole_0(A_60) | ~r2_hidden(C_61, k2_relat_1(A_60)))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.07/1.24  tff(c_92, plain, (![A_62]: (~v1_xboole_0(A_62) | k2_relat_1(A_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_76])).
% 2.07/1.24  tff(c_96, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_92])).
% 2.07/1.24  tff(c_75, plain, (![A_58, C_59]: (~v1_xboole_0(A_58) | ~r2_hidden(C_59, k2_relat_1(A_58)))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.07/1.24  tff(c_100, plain, (![C_59]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_96, c_75])).
% 2.07/1.24  tff(c_128, plain, (![C_65]: (~r2_hidden(C_65, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_100])).
% 2.07/1.24  tff(c_152, plain, (![C_66]: (~r2_hidden(C_66, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_128])).
% 2.07/1.24  tff(c_164, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_152])).
% 2.07/1.24  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_164])).
% 2.07/1.24  tff(c_175, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.07/1.24  tff(c_430, plain, (![A_89, C_90]: (r2_hidden(k4_tarski('#skF_10'(A_89, k2_relat_1(A_89), C_90), C_90), A_89) | ~r2_hidden(C_90, k2_relat_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.24  tff(c_176, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.07/1.24  tff(c_195, plain, (![C_77, A_78]: (r2_hidden(k4_tarski(C_77, '#skF_6'(A_78, k1_relat_1(A_78), C_77)), A_78) | ~r2_hidden(C_77, k1_relat_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.07/1.24  tff(c_212, plain, (![A_79, C_80]: (~v1_xboole_0(A_79) | ~r2_hidden(C_80, k1_relat_1(A_79)))), inference(resolution, [status(thm)], [c_195, c_2])).
% 2.07/1.24  tff(c_223, plain, (![C_80]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_176, c_212])).
% 2.07/1.24  tff(c_231, plain, (![C_80]: (~r2_hidden(C_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_223])).
% 2.07/1.24  tff(c_458, plain, (![C_91]: (~r2_hidden(C_91, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_430, c_231])).
% 2.07/1.24  tff(c_470, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_458])).
% 2.07/1.24  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_470])).
% 2.07/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  Inference rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Ref     : 0
% 2.07/1.24  #Sup     : 95
% 2.07/1.24  #Fact    : 0
% 2.07/1.24  #Define  : 0
% 2.07/1.24  #Split   : 1
% 2.07/1.24  #Chain   : 0
% 2.07/1.24  #Close   : 0
% 2.07/1.24  
% 2.07/1.24  Ordering : KBO
% 2.07/1.24  
% 2.07/1.24  Simplification rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Subsume      : 13
% 2.07/1.24  #Demod        : 44
% 2.07/1.24  #Tautology    : 43
% 2.07/1.24  #SimpNegUnit  : 3
% 2.07/1.24  #BackRed      : 0
% 2.07/1.24  
% 2.07/1.24  #Partial instantiations: 0
% 2.07/1.24  #Strategies tried      : 1
% 2.07/1.24  
% 2.07/1.24  Timing (in seconds)
% 2.07/1.24  ----------------------
% 2.07/1.25  Preprocessing        : 0.29
% 2.07/1.25  Parsing              : 0.15
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.20
% 2.07/1.25  Inferencing          : 0.07
% 2.07/1.25  Reduction            : 0.05
% 2.07/1.25  Demodulation         : 0.04
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.04
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.51
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
