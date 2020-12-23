%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   34 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  92 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_92,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    r2_hidden('#skF_6',k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_543,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden(k1_mcart_1(A_132),B_133)
      | ~ r2_hidden(A_132,k2_zfmisc_1(B_133,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_554,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_543])).

tff(c_72,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_6'),'#skF_8')
    | k1_mcart_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_124,plain,(
    k1_mcart_1('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_54,plain,(
    ! [A_39] : k2_xboole_0(A_39,k1_tarski(A_39)) = k1_ordinal1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_140,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | r2_hidden(D_66,k2_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [D_66,A_39] :
      ( ~ r2_hidden(D_66,k1_tarski(A_39))
      | r2_hidden(D_66,k1_ordinal1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_140])).

tff(c_561,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k1_ordinal1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_554,c_146])).

tff(c_56,plain,(
    ! [B_41,A_40] :
      ( B_41 = A_40
      | r2_hidden(A_40,B_41)
      | ~ r2_hidden(A_40,k1_ordinal1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_584,plain,
    ( k1_mcart_1('#skF_6') = '#skF_7'
    | r2_hidden(k1_mcart_1('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_561,c_56])).

tff(c_590,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_584])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_596,plain,(
    ! [A_137,B_138,C_139] :
      ( ~ r1_xboole_0(A_137,B_138)
      | ~ r2_hidden(C_139,B_138)
      | ~ r2_hidden(C_139,A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2152,plain,(
    ! [C_363,B_364,A_365] :
      ( ~ r2_hidden(C_363,B_364)
      | ~ r2_hidden(C_363,k1_tarski(A_365))
      | r2_hidden(A_365,B_364) ) ),
    inference(resolution,[status(thm)],[c_42,c_596])).

tff(c_2723,plain,(
    ! [A_375] :
      ( ~ r2_hidden(k1_mcart_1('#skF_6'),k1_tarski(A_375))
      | r2_hidden(A_375,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_590,c_2152])).

tff(c_2727,plain,(
    r2_hidden('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_554,c_2723])).

tff(c_62,plain,(
    ! [B_43,A_42] :
      ( ~ r1_tarski(B_43,A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2732,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_2727,c_62])).

tff(c_2737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2732])).

tff(c_2738,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3010,plain,(
    ! [A_421,C_422,B_423] :
      ( r2_hidden(k2_mcart_1(A_421),C_422)
      | ~ r2_hidden(A_421,k2_zfmisc_1(B_423,C_422)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3018,plain,(
    r2_hidden(k2_mcart_1('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_3010])).

tff(c_3024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2738,c_3018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.84  
% 4.74/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_ordinal1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_8
% 4.74/1.85  
% 4.74/1.85  %Foreground sorts:
% 4.74/1.85  
% 4.74/1.85  
% 4.74/1.85  %Background operators:
% 4.74/1.85  
% 4.74/1.85  
% 4.74/1.85  %Foreground operators:
% 4.74/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.74/1.85  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.74/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.74/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.74/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.74/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.74/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.74/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.74/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.74/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.74/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.74/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.74/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.74/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.74/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.74/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.85  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.74/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.85  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.74/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.74/1.85  
% 4.74/1.86  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.74/1.86  tff(f_120, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 4.74/1.86  tff(f_109, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.74/1.86  tff(f_92, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.74/1.86  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.74/1.86  tff(f_98, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 4.74/1.86  tff(f_78, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.74/1.86  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.74/1.86  tff(f_103, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.74/1.86  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.74/1.86  tff(c_74, plain, (r2_hidden('#skF_6', k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.74/1.86  tff(c_543, plain, (![A_132, B_133, C_134]: (r2_hidden(k1_mcart_1(A_132), B_133) | ~r2_hidden(A_132, k2_zfmisc_1(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.74/1.86  tff(c_554, plain, (r2_hidden(k1_mcart_1('#skF_6'), k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_543])).
% 4.74/1.86  tff(c_72, plain, (~r2_hidden(k2_mcart_1('#skF_6'), '#skF_8') | k1_mcart_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.74/1.86  tff(c_124, plain, (k1_mcart_1('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_72])).
% 4.74/1.86  tff(c_54, plain, (![A_39]: (k2_xboole_0(A_39, k1_tarski(A_39))=k1_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.74/1.86  tff(c_140, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | r2_hidden(D_66, k2_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.74/1.86  tff(c_146, plain, (![D_66, A_39]: (~r2_hidden(D_66, k1_tarski(A_39)) | r2_hidden(D_66, k1_ordinal1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_140])).
% 4.74/1.86  tff(c_561, plain, (r2_hidden(k1_mcart_1('#skF_6'), k1_ordinal1('#skF_7'))), inference(resolution, [status(thm)], [c_554, c_146])).
% 4.74/1.86  tff(c_56, plain, (![B_41, A_40]: (B_41=A_40 | r2_hidden(A_40, B_41) | ~r2_hidden(A_40, k1_ordinal1(B_41)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.74/1.86  tff(c_584, plain, (k1_mcart_1('#skF_6')='#skF_7' | r2_hidden(k1_mcart_1('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_561, c_56])).
% 4.74/1.86  tff(c_590, plain, (r2_hidden(k1_mcart_1('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_124, c_584])).
% 4.74/1.86  tff(c_42, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.74/1.86  tff(c_596, plain, (![A_137, B_138, C_139]: (~r1_xboole_0(A_137, B_138) | ~r2_hidden(C_139, B_138) | ~r2_hidden(C_139, A_137))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.74/1.86  tff(c_2152, plain, (![C_363, B_364, A_365]: (~r2_hidden(C_363, B_364) | ~r2_hidden(C_363, k1_tarski(A_365)) | r2_hidden(A_365, B_364))), inference(resolution, [status(thm)], [c_42, c_596])).
% 4.74/1.86  tff(c_2723, plain, (![A_375]: (~r2_hidden(k1_mcart_1('#skF_6'), k1_tarski(A_375)) | r2_hidden(A_375, '#skF_7'))), inference(resolution, [status(thm)], [c_590, c_2152])).
% 4.74/1.86  tff(c_2727, plain, (r2_hidden('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_554, c_2723])).
% 4.74/1.86  tff(c_62, plain, (![B_43, A_42]: (~r1_tarski(B_43, A_42) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.74/1.86  tff(c_2732, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_2727, c_62])).
% 4.74/1.86  tff(c_2737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2732])).
% 4.74/1.86  tff(c_2738, plain, (~r2_hidden(k2_mcart_1('#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 4.74/1.86  tff(c_3010, plain, (![A_421, C_422, B_423]: (r2_hidden(k2_mcart_1(A_421), C_422) | ~r2_hidden(A_421, k2_zfmisc_1(B_423, C_422)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.74/1.86  tff(c_3018, plain, (r2_hidden(k2_mcart_1('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_74, c_3010])).
% 4.74/1.86  tff(c_3024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2738, c_3018])).
% 4.74/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.86  
% 4.74/1.86  Inference rules
% 4.74/1.86  ----------------------
% 4.74/1.86  #Ref     : 0
% 4.74/1.86  #Sup     : 616
% 4.74/1.86  #Fact    : 6
% 4.74/1.86  #Define  : 0
% 4.74/1.86  #Split   : 1
% 4.74/1.86  #Chain   : 0
% 4.74/1.86  #Close   : 0
% 4.74/1.86  
% 4.74/1.86  Ordering : KBO
% 4.74/1.86  
% 4.74/1.86  Simplification rules
% 4.74/1.86  ----------------------
% 4.74/1.86  #Subsume      : 69
% 4.74/1.86  #Demod        : 10
% 4.74/1.86  #Tautology    : 38
% 4.74/1.86  #SimpNegUnit  : 3
% 4.74/1.86  #BackRed      : 0
% 4.74/1.86  
% 4.74/1.86  #Partial instantiations: 0
% 4.74/1.86  #Strategies tried      : 1
% 4.74/1.86  
% 4.74/1.86  Timing (in seconds)
% 4.74/1.86  ----------------------
% 4.74/1.86  Preprocessing        : 0.33
% 4.74/1.86  Parsing              : 0.17
% 4.74/1.86  CNF conversion       : 0.02
% 4.74/1.86  Main loop            : 0.77
% 4.74/1.86  Inferencing          : 0.25
% 4.74/1.86  Reduction            : 0.21
% 4.74/1.86  Demodulation         : 0.13
% 4.74/1.86  BG Simplification    : 0.03
% 4.74/1.86  Subsumption          : 0.22
% 4.74/1.86  Abstraction          : 0.03
% 4.74/1.86  MUC search           : 0.00
% 4.74/1.86  Cooper               : 0.00
% 4.74/1.86  Total                : 1.12
% 4.74/1.86  Index Insertion      : 0.00
% 4.74/1.86  Index Deletion       : 0.00
% 4.74/1.86  Index Matching       : 0.00
% 4.74/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
