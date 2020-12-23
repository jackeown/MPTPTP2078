%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   64 (  89 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 130 expanded)
%              Number of equality atoms :   34 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_70,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_376,plain,(
    ! [D_103,B_104,A_105] :
      ( ~ r2_hidden(D_103,B_104)
      | r2_hidden(D_103,k2_xboole_0(A_105,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_392,plain,(
    ! [D_106] :
      ( ~ r2_hidden(D_106,'#skF_8')
      | r2_hidden(D_106,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_376])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_397,plain,(
    ! [D_107] :
      ( D_107 = '#skF_6'
      | ~ r2_hidden(D_107,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_392,c_26])).

tff(c_401,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_397])).

tff(c_404,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_401])).

tff(c_408,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_20])).

tff(c_411,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_408])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    ! [A_55,B_56] : r1_tarski(A_55,k2_xboole_0(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_79])).

tff(c_497,plain,(
    ! [B_115,A_116] :
      ( k1_tarski(B_115) = A_116
      | k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,k1_tarski(B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_503,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_82,c_497])).

tff(c_511,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_503])).

tff(c_38,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_756,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(k2_tarski(A_127,B_128),C_129)
      | ~ r2_hidden(B_128,C_129)
      | ~ r2_hidden(A_127,C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1949,plain,(
    ! [A_187,C_188] :
      ( r1_tarski(k1_tarski(A_187),C_188)
      | ~ r2_hidden(A_187,C_188)
      | ~ r2_hidden(A_187,C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_756])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2008,plain,(
    ! [A_192,C_193] :
      ( k2_xboole_0(k1_tarski(A_192),C_193) = C_193
      | ~ r2_hidden(A_192,C_193) ) ),
    inference(resolution,[status(thm)],[c_1949,c_22])).

tff(c_24,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2129,plain,(
    ! [A_194,C_195] :
      ( r1_tarski(k1_tarski(A_194),C_195)
      | ~ r2_hidden(A_194,C_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_24])).

tff(c_2157,plain,(
    ! [C_196] :
      ( r1_tarski('#skF_7',C_196)
      | ~ r2_hidden('#skF_6',C_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_2129])).

tff(c_2238,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_411,c_2157])).

tff(c_2275,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2238,c_22])).

tff(c_518,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_72])).

tff(c_2276,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_518])).

tff(c_2278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:11:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.78  
% 4.01/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.79  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.01/1.79  
% 4.01/1.79  %Foreground sorts:
% 4.01/1.79  
% 4.01/1.79  
% 4.01/1.79  %Background operators:
% 4.01/1.79  
% 4.01/1.79  
% 4.01/1.79  %Foreground operators:
% 4.01/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.01/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.01/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.01/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.01/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.01/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.01/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.01/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.01/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.01/1.79  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.01/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.01/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.01/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.01/1.79  
% 4.01/1.80  tff(f_96, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.01/1.80  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.01/1.80  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.01/1.80  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.01/1.80  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.01/1.80  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.01/1.80  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.01/1.80  tff(f_83, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.01/1.80  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.01/1.80  tff(c_70, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.01/1.80  tff(c_66, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.01/1.80  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.01/1.80  tff(c_72, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.01/1.80  tff(c_376, plain, (![D_103, B_104, A_105]: (~r2_hidden(D_103, B_104) | r2_hidden(D_103, k2_xboole_0(A_105, B_104)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.01/1.80  tff(c_392, plain, (![D_106]: (~r2_hidden(D_106, '#skF_8') | r2_hidden(D_106, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_376])).
% 4.01/1.80  tff(c_26, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.01/1.80  tff(c_397, plain, (![D_107]: (D_107='#skF_6' | ~r2_hidden(D_107, '#skF_8'))), inference(resolution, [status(thm)], [c_392, c_26])).
% 4.01/1.80  tff(c_401, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_397])).
% 4.01/1.80  tff(c_404, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_66, c_401])).
% 4.01/1.80  tff(c_408, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_404, c_20])).
% 4.01/1.80  tff(c_411, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_66, c_408])).
% 4.01/1.80  tff(c_68, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.01/1.80  tff(c_79, plain, (![A_55, B_56]: (r1_tarski(A_55, k2_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.01/1.80  tff(c_82, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_79])).
% 4.01/1.80  tff(c_497, plain, (![B_115, A_116]: (k1_tarski(B_115)=A_116 | k1_xboole_0=A_116 | ~r1_tarski(A_116, k1_tarski(B_115)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.80  tff(c_503, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_82, c_497])).
% 4.01/1.80  tff(c_511, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_68, c_503])).
% 4.01/1.80  tff(c_38, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.80  tff(c_756, plain, (![A_127, B_128, C_129]: (r1_tarski(k2_tarski(A_127, B_128), C_129) | ~r2_hidden(B_128, C_129) | ~r2_hidden(A_127, C_129))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.80  tff(c_1949, plain, (![A_187, C_188]: (r1_tarski(k1_tarski(A_187), C_188) | ~r2_hidden(A_187, C_188) | ~r2_hidden(A_187, C_188))), inference(superposition, [status(thm), theory('equality')], [c_38, c_756])).
% 4.01/1.80  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.01/1.80  tff(c_2008, plain, (![A_192, C_193]: (k2_xboole_0(k1_tarski(A_192), C_193)=C_193 | ~r2_hidden(A_192, C_193))), inference(resolution, [status(thm)], [c_1949, c_22])).
% 4.01/1.80  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.01/1.80  tff(c_2129, plain, (![A_194, C_195]: (r1_tarski(k1_tarski(A_194), C_195) | ~r2_hidden(A_194, C_195))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_24])).
% 4.01/1.80  tff(c_2157, plain, (![C_196]: (r1_tarski('#skF_7', C_196) | ~r2_hidden('#skF_6', C_196))), inference(superposition, [status(thm), theory('equality')], [c_511, c_2129])).
% 4.01/1.80  tff(c_2238, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_411, c_2157])).
% 4.01/1.80  tff(c_2275, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_2238, c_22])).
% 4.01/1.80  tff(c_518, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_72])).
% 4.01/1.80  tff(c_2276, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_518])).
% 4.01/1.80  tff(c_2278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2276])).
% 4.01/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.80  
% 4.01/1.80  Inference rules
% 4.01/1.80  ----------------------
% 4.01/1.80  #Ref     : 0
% 4.01/1.80  #Sup     : 515
% 4.01/1.80  #Fact    : 4
% 4.01/1.80  #Define  : 0
% 4.01/1.80  #Split   : 7
% 4.01/1.80  #Chain   : 0
% 4.01/1.80  #Close   : 0
% 4.01/1.80  
% 4.01/1.80  Ordering : KBO
% 4.01/1.80  
% 4.01/1.80  Simplification rules
% 4.01/1.80  ----------------------
% 4.01/1.80  #Subsume      : 48
% 4.01/1.80  #Demod        : 289
% 4.01/1.80  #Tautology    : 300
% 4.01/1.80  #SimpNegUnit  : 23
% 4.01/1.80  #BackRed      : 29
% 4.01/1.80  
% 4.01/1.80  #Partial instantiations: 0
% 4.01/1.80  #Strategies tried      : 1
% 4.01/1.80  
% 4.01/1.80  Timing (in seconds)
% 4.01/1.80  ----------------------
% 4.01/1.80  Preprocessing        : 0.36
% 4.01/1.80  Parsing              : 0.17
% 4.01/1.80  CNF conversion       : 0.03
% 4.01/1.80  Main loop            : 0.67
% 4.01/1.80  Inferencing          : 0.22
% 4.01/1.80  Reduction            : 0.24
% 4.01/1.80  Demodulation         : 0.18
% 4.01/1.80  BG Simplification    : 0.03
% 4.01/1.80  Subsumption          : 0.12
% 4.01/1.80  Abstraction          : 0.03
% 4.01/1.80  MUC search           : 0.00
% 4.01/1.80  Cooper               : 0.00
% 4.01/1.80  Total                : 1.06
% 4.01/1.80  Index Insertion      : 0.00
% 4.01/1.80  Index Deletion       : 0.00
% 4.01/1.80  Index Matching       : 0.00
% 4.01/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
