%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 107 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 231 expanded)
%              Number of equality atoms :   60 ( 204 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_66,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_94,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_268,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(A_44,B_45)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_287,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_268])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_885,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(B_88) = A_89
      | k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_tarski(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1172,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(B_103) = A_104
      | k1_xboole_0 = A_104
      | k4_xboole_0(A_104,k1_tarski(B_103)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_885])).

tff(c_1190,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_1172])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_94,c_1190])).

tff(c_1208,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1229,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1208,c_68])).

tff(c_1207,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1209,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_70])).

tff(c_1945,plain,(
    ! [D_145,B_146,A_147] :
      ( ~ r2_hidden(D_145,B_146)
      | r2_hidden(D_145,k2_xboole_0(A_147,B_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2015,plain,(
    ! [D_153] :
      ( ~ r2_hidden(D_153,'#skF_8')
      | r2_hidden(D_153,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_1945])).

tff(c_1234,plain,(
    ! [C_105,A_106] :
      ( C_105 = A_106
      | ~ r2_hidden(C_105,k1_tarski(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1237,plain,(
    ! [C_105] :
      ( C_105 = '#skF_6'
      | ~ r2_hidden(C_105,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1208,c_1234])).

tff(c_2026,plain,(
    ! [D_154] :
      ( D_154 = '#skF_6'
      | ~ r2_hidden(D_154,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2015,c_1237])).

tff(c_2034,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_2026])).

tff(c_2039,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1207,c_2034])).

tff(c_2043,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2039,c_22])).

tff(c_2046,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1207,c_2043])).

tff(c_1793,plain,(
    ! [A_140,B_141] :
      ( k2_xboole_0(k1_tarski(A_140),B_141) = B_141
      | ~ r2_hidden(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1846,plain,(
    ! [B_141] :
      ( k2_xboole_0('#skF_7',B_141) = B_141
      | ~ r2_hidden('#skF_6',B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1208,c_1793])).

tff(c_2056,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2046,c_1846])).

tff(c_2057,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1209])).

tff(c_2059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1229,c_2057])).

tff(c_2060,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2061,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_28,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2063,plain,(
    ! [A_13] : k2_xboole_0(A_13,'#skF_7') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_28])).

tff(c_2089,plain,(
    ! [B_159,A_160] : k2_xboole_0(B_159,A_160) = k2_xboole_0(A_160,B_159) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2112,plain,(
    k2_xboole_0('#skF_8','#skF_7') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_70])).

tff(c_2144,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_2112])).

tff(c_2146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2060,c_2144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.29/1.54  
% 3.29/1.54  %Foreground sorts:
% 3.29/1.54  
% 3.29/1.54  
% 3.29/1.54  %Background operators:
% 3.29/1.54  
% 3.29/1.54  
% 3.29/1.54  %Foreground operators:
% 3.29/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.54  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.29/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.29/1.54  
% 3.29/1.55  tff(f_108, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.29/1.55  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.29/1.55  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.29/1.55  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.29/1.55  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.29/1.55  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.29/1.55  tff(f_75, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.29/1.55  tff(f_79, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.29/1.55  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.29/1.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.29/1.55  tff(c_66, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.55  tff(c_92, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_66])).
% 3.29/1.55  tff(c_64, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.55  tff(c_94, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_64])).
% 3.29/1.55  tff(c_70, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.55  tff(c_268, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(A_44, B_45))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.55  tff(c_287, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70, c_268])).
% 3.29/1.55  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.55  tff(c_885, plain, (![B_88, A_89]: (k1_tarski(B_88)=A_89 | k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_tarski(B_88)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.55  tff(c_1172, plain, (![B_103, A_104]: (k1_tarski(B_103)=A_104 | k1_xboole_0=A_104 | k4_xboole_0(A_104, k1_tarski(B_103))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_885])).
% 3.29/1.55  tff(c_1190, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_287, c_1172])).
% 3.29/1.55  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_94, c_1190])).
% 3.29/1.55  tff(c_1208, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_64])).
% 3.29/1.55  tff(c_68, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.55  tff(c_1229, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1208, c_68])).
% 3.29/1.55  tff(c_1207, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 3.29/1.55  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.29/1.55  tff(c_1209, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_70])).
% 3.29/1.55  tff(c_1945, plain, (![D_145, B_146, A_147]: (~r2_hidden(D_145, B_146) | r2_hidden(D_145, k2_xboole_0(A_147, B_146)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.29/1.55  tff(c_2015, plain, (![D_153]: (~r2_hidden(D_153, '#skF_8') | r2_hidden(D_153, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1209, c_1945])).
% 3.29/1.55  tff(c_1234, plain, (![C_105, A_106]: (C_105=A_106 | ~r2_hidden(C_105, k1_tarski(A_106)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.29/1.55  tff(c_1237, plain, (![C_105]: (C_105='#skF_6' | ~r2_hidden(C_105, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1208, c_1234])).
% 3.29/1.55  tff(c_2026, plain, (![D_154]: (D_154='#skF_6' | ~r2_hidden(D_154, '#skF_8'))), inference(resolution, [status(thm)], [c_2015, c_1237])).
% 3.29/1.55  tff(c_2034, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_2026])).
% 3.29/1.55  tff(c_2039, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1207, c_2034])).
% 3.29/1.55  tff(c_2043, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2039, c_22])).
% 3.29/1.55  tff(c_2046, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1207, c_2043])).
% 3.29/1.55  tff(c_1793, plain, (![A_140, B_141]: (k2_xboole_0(k1_tarski(A_140), B_141)=B_141 | ~r2_hidden(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.29/1.55  tff(c_1846, plain, (![B_141]: (k2_xboole_0('#skF_7', B_141)=B_141 | ~r2_hidden('#skF_6', B_141))), inference(superposition, [status(thm), theory('equality')], [c_1208, c_1793])).
% 3.29/1.55  tff(c_2056, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_2046, c_1846])).
% 3.29/1.55  tff(c_2057, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1209])).
% 3.29/1.55  tff(c_2059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1229, c_2057])).
% 3.29/1.55  tff(c_2060, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 3.29/1.55  tff(c_2061, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 3.29/1.55  tff(c_28, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/1.55  tff(c_2063, plain, (![A_13]: (k2_xboole_0(A_13, '#skF_7')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_28])).
% 3.29/1.55  tff(c_2089, plain, (![B_159, A_160]: (k2_xboole_0(B_159, A_160)=k2_xboole_0(A_160, B_159))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.55  tff(c_2112, plain, (k2_xboole_0('#skF_8', '#skF_7')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2089, c_70])).
% 3.29/1.55  tff(c_2144, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_2112])).
% 3.29/1.55  tff(c_2146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2060, c_2144])).
% 3.29/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.55  
% 3.29/1.55  Inference rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Ref     : 0
% 3.29/1.55  #Sup     : 497
% 3.29/1.55  #Fact    : 0
% 3.29/1.55  #Define  : 0
% 3.29/1.55  #Split   : 4
% 3.29/1.55  #Chain   : 0
% 3.29/1.55  #Close   : 0
% 3.29/1.55  
% 3.29/1.55  Ordering : KBO
% 3.29/1.55  
% 3.29/1.55  Simplification rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Subsume      : 33
% 3.29/1.55  #Demod        : 203
% 3.29/1.55  #Tautology    : 352
% 3.29/1.55  #SimpNegUnit  : 14
% 3.29/1.55  #BackRed      : 28
% 3.29/1.55  
% 3.29/1.55  #Partial instantiations: 0
% 3.29/1.55  #Strategies tried      : 1
% 3.29/1.55  
% 3.29/1.55  Timing (in seconds)
% 3.29/1.55  ----------------------
% 3.29/1.55  Preprocessing        : 0.31
% 3.29/1.55  Parsing              : 0.16
% 3.29/1.55  CNF conversion       : 0.02
% 3.29/1.55  Main loop            : 0.47
% 3.29/1.55  Inferencing          : 0.16
% 3.29/1.55  Reduction            : 0.16
% 3.29/1.55  Demodulation         : 0.12
% 3.29/1.55  BG Simplification    : 0.02
% 3.29/1.55  Subsumption          : 0.08
% 3.29/1.55  Abstraction          : 0.02
% 3.29/1.55  MUC search           : 0.00
% 3.29/1.55  Cooper               : 0.00
% 3.29/1.55  Total                : 0.81
% 3.29/1.55  Index Insertion      : 0.00
% 3.29/1.55  Index Deletion       : 0.00
% 3.29/1.55  Index Matching       : 0.00
% 3.29/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
