%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 109 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 234 expanded)
%              Number of equality atoms :   49 ( 195 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(c_70,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_83,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_52,plain,(
    ! [B_33] : r1_tarski(k1_tarski(B_33),k1_tarski(B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_591,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,C_105)
      | ~ r1_tarski(k2_xboole_0(A_104,B_106),C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_608,plain,(
    ! [C_107] :
      ( r1_tarski('#skF_7',C_107)
      | ~ r1_tarski(k1_tarski('#skF_6'),C_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_591])).

tff(c_623,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_608])).

tff(c_772,plain,(
    ! [B_127,A_128] :
      ( k1_tarski(B_127) = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,k1_tarski(B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_775,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_623,c_772])).

tff(c_786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_83,c_775])).

tff(c_787,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_788,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_26,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_789,plain,(
    ! [A_14] : r1_tarski('#skF_7',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_26])).

tff(c_828,plain,(
    ! [A_139,B_140] :
      ( k2_xboole_0(A_139,B_140) = B_140
      | ~ r1_tarski(A_139,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_844,plain,(
    ! [A_14] : k2_xboole_0('#skF_7',A_14) = A_14 ),
    inference(resolution,[status(thm)],[c_789,c_828])).

tff(c_845,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_74])).

tff(c_847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_845])).

tff(c_849,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_912,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_849,c_72])).

tff(c_848,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_850,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_74])).

tff(c_1161,plain,(
    ! [D_173,B_174,A_175] :
      ( ~ r2_hidden(D_173,B_174)
      | r2_hidden(D_173,k2_xboole_0(A_175,B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1183,plain,(
    ! [D_176] :
      ( ~ r2_hidden(D_176,'#skF_8')
      | r2_hidden(D_176,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_1161])).

tff(c_914,plain,(
    ! [C_150,A_151] :
      ( C_150 = A_151
      | ~ r2_hidden(C_150,k1_tarski(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_921,plain,(
    ! [C_150] :
      ( C_150 = '#skF_6'
      | ~ r2_hidden(C_150,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_914])).

tff(c_1188,plain,(
    ! [D_177] :
      ( D_177 = '#skF_6'
      | ~ r2_hidden(D_177,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1183,c_921])).

tff(c_1192,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_1188])).

tff(c_1195,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_848,c_1192])).

tff(c_1199,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1195,c_20])).

tff(c_1202,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_848,c_1199])).

tff(c_1209,plain,(
    ! [A_178,B_179] :
      ( k2_xboole_0(k1_tarski(A_178),B_179) = B_179
      | ~ r2_hidden(A_178,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1252,plain,(
    ! [B_180] :
      ( k2_xboole_0('#skF_7',B_180) = B_180
      | ~ r2_hidden('#skF_6',B_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_1209])).

tff(c_1279,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1202,c_1252])).

tff(c_1290,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_850])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_912,c_1290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.86/1.45  
% 2.86/1.45  %Foreground sorts:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Background operators:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Foreground operators:
% 2.86/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.86/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.86/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.45  
% 2.86/1.46  tff(f_113, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.86/1.46  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.86/1.46  tff(f_46, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.86/1.46  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.86/1.46  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.86/1.46  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.86/1.46  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.86/1.46  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.86/1.46  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.86/1.46  tff(c_70, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.46  tff(c_84, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_70])).
% 2.86/1.46  tff(c_68, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.46  tff(c_83, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_68])).
% 2.86/1.46  tff(c_52, plain, (![B_33]: (r1_tarski(k1_tarski(B_33), k1_tarski(B_33)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.46  tff(c_74, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.46  tff(c_591, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, C_105) | ~r1_tarski(k2_xboole_0(A_104, B_106), C_105))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.46  tff(c_608, plain, (![C_107]: (r1_tarski('#skF_7', C_107) | ~r1_tarski(k1_tarski('#skF_6'), C_107))), inference(superposition, [status(thm), theory('equality')], [c_74, c_591])).
% 2.86/1.46  tff(c_623, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_608])).
% 2.86/1.46  tff(c_772, plain, (![B_127, A_128]: (k1_tarski(B_127)=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, k1_tarski(B_127)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.46  tff(c_775, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_623, c_772])).
% 2.86/1.46  tff(c_786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_83, c_775])).
% 2.86/1.46  tff(c_787, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 2.86/1.46  tff(c_788, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_70])).
% 2.86/1.46  tff(c_26, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.46  tff(c_789, plain, (![A_14]: (r1_tarski('#skF_7', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_788, c_26])).
% 2.86/1.46  tff(c_828, plain, (![A_139, B_140]: (k2_xboole_0(A_139, B_140)=B_140 | ~r1_tarski(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.46  tff(c_844, plain, (![A_14]: (k2_xboole_0('#skF_7', A_14)=A_14)), inference(resolution, [status(thm)], [c_789, c_828])).
% 2.86/1.46  tff(c_845, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_844, c_74])).
% 2.86/1.46  tff(c_847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_845])).
% 2.86/1.46  tff(c_849, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 2.86/1.46  tff(c_72, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.46  tff(c_912, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_849, c_849, c_72])).
% 2.86/1.46  tff(c_848, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_68])).
% 2.86/1.46  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.46  tff(c_850, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_849, c_74])).
% 2.86/1.46  tff(c_1161, plain, (![D_173, B_174, A_175]: (~r2_hidden(D_173, B_174) | r2_hidden(D_173, k2_xboole_0(A_175, B_174)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.46  tff(c_1183, plain, (![D_176]: (~r2_hidden(D_176, '#skF_8') | r2_hidden(D_176, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_850, c_1161])).
% 2.86/1.46  tff(c_914, plain, (![C_150, A_151]: (C_150=A_151 | ~r2_hidden(C_150, k1_tarski(A_151)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.46  tff(c_921, plain, (![C_150]: (C_150='#skF_6' | ~r2_hidden(C_150, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_849, c_914])).
% 2.86/1.46  tff(c_1188, plain, (![D_177]: (D_177='#skF_6' | ~r2_hidden(D_177, '#skF_8'))), inference(resolution, [status(thm)], [c_1183, c_921])).
% 2.86/1.46  tff(c_1192, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_1188])).
% 2.86/1.46  tff(c_1195, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_848, c_1192])).
% 2.86/1.46  tff(c_1199, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1195, c_20])).
% 2.86/1.46  tff(c_1202, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_848, c_1199])).
% 2.86/1.46  tff(c_1209, plain, (![A_178, B_179]: (k2_xboole_0(k1_tarski(A_178), B_179)=B_179 | ~r2_hidden(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.46  tff(c_1252, plain, (![B_180]: (k2_xboole_0('#skF_7', B_180)=B_180 | ~r2_hidden('#skF_6', B_180))), inference(superposition, [status(thm), theory('equality')], [c_849, c_1209])).
% 2.86/1.46  tff(c_1279, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1202, c_1252])).
% 2.86/1.46  tff(c_1290, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1279, c_850])).
% 2.86/1.46  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_912, c_1290])).
% 2.86/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.46  
% 2.86/1.46  Inference rules
% 2.86/1.46  ----------------------
% 2.86/1.46  #Ref     : 0
% 2.86/1.46  #Sup     : 285
% 2.86/1.46  #Fact    : 0
% 2.86/1.46  #Define  : 0
% 2.86/1.46  #Split   : 4
% 2.86/1.46  #Chain   : 0
% 2.86/1.46  #Close   : 0
% 2.86/1.46  
% 2.86/1.46  Ordering : KBO
% 2.86/1.46  
% 2.86/1.46  Simplification rules
% 2.86/1.46  ----------------------
% 2.86/1.46  #Subsume      : 19
% 2.86/1.46  #Demod        : 95
% 2.86/1.46  #Tautology    : 177
% 2.86/1.46  #SimpNegUnit  : 14
% 2.86/1.46  #BackRed      : 9
% 2.86/1.46  
% 2.86/1.46  #Partial instantiations: 0
% 2.86/1.46  #Strategies tried      : 1
% 2.86/1.46  
% 2.86/1.46  Timing (in seconds)
% 2.86/1.46  ----------------------
% 3.12/1.46  Preprocessing        : 0.31
% 3.12/1.46  Parsing              : 0.16
% 3.12/1.46  CNF conversion       : 0.02
% 3.12/1.46  Main loop            : 0.38
% 3.12/1.46  Inferencing          : 0.14
% 3.12/1.46  Reduction            : 0.12
% 3.12/1.46  Demodulation         : 0.09
% 3.12/1.46  BG Simplification    : 0.02
% 3.12/1.46  Subsumption          : 0.06
% 3.12/1.46  Abstraction          : 0.02
% 3.12/1.46  MUC search           : 0.00
% 3.12/1.46  Cooper               : 0.00
% 3.12/1.46  Total                : 0.72
% 3.12/1.46  Index Insertion      : 0.00
% 3.12/1.46  Index Deletion       : 0.00
% 3.12/1.46  Index Matching       : 0.00
% 3.12/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
