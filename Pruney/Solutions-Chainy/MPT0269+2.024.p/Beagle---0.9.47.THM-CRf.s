%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   50 (  66 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_446,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,k1_tarski(B_78)) = A_77
      | r2_hidden(B_78,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_475,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_62])).

tff(c_505,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_475])).

tff(c_653,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84,B_85),A_84)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1694,plain,(
    ! [A_134,B_135] :
      ( '#skF_1'(k1_tarski(A_134),B_135) = A_134
      | r1_tarski(k1_tarski(A_134),B_135) ) ),
    inference(resolution,[status(thm)],[c_653,c_36])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2563,plain,(
    ! [A_177,B_178] :
      ( k4_xboole_0(k1_tarski(A_177),B_178) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_177),B_178) = A_177 ) ),
    inference(resolution,[status(thm)],[c_1694,c_18])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_293,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2120,plain,(
    ! [B_151,A_152] :
      ( B_151 = A_152
      | ~ r1_tarski(B_151,A_152)
      | k4_xboole_0(A_152,B_151) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_2464,plain,(
    ! [B_173,A_174] :
      ( B_173 = A_174
      | k4_xboole_0(B_173,A_174) != k1_xboole_0
      | k4_xboole_0(A_174,B_173) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_2120])).

tff(c_2480,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2464])).

tff(c_2499,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2480])).

tff(c_2692,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_2499])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2733,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2692,c_4])).

tff(c_2743,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_2733])).

tff(c_303,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_2821,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2743,c_303])).

tff(c_2837,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2821])).

tff(c_2839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2837])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:37:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.70  
% 4.06/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.70  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.06/1.70  
% 4.06/1.70  %Foreground sorts:
% 4.06/1.70  
% 4.06/1.70  
% 4.06/1.70  %Background operators:
% 4.06/1.70  
% 4.06/1.70  
% 4.06/1.70  %Foreground operators:
% 4.06/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.06/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.06/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.06/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.06/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.06/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.06/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.06/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.06/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.06/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.06/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.06/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.70  
% 4.06/1.72  tff(f_90, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.06/1.72  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.06/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.06/1.72  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.06/1.72  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.06/1.72  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.06/1.72  tff(c_58, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.72  tff(c_62, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.72  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.72  tff(c_446, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k1_tarski(B_78))=A_77 | r2_hidden(B_78, A_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.06/1.72  tff(c_475, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_446, c_62])).
% 4.06/1.72  tff(c_505, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_475])).
% 4.06/1.72  tff(c_653, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84, B_85), A_84) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.72  tff(c_36, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.06/1.72  tff(c_1694, plain, (![A_134, B_135]: ('#skF_1'(k1_tarski(A_134), B_135)=A_134 | r1_tarski(k1_tarski(A_134), B_135))), inference(resolution, [status(thm)], [c_653, c_36])).
% 4.06/1.72  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.06/1.72  tff(c_2563, plain, (![A_177, B_178]: (k4_xboole_0(k1_tarski(A_177), B_178)=k1_xboole_0 | '#skF_1'(k1_tarski(A_177), B_178)=A_177)), inference(resolution, [status(thm)], [c_1694, c_18])).
% 4.06/1.72  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.06/1.72  tff(c_293, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.06/1.72  tff(c_2120, plain, (![B_151, A_152]: (B_151=A_152 | ~r1_tarski(B_151, A_152) | k4_xboole_0(A_152, B_151)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_293])).
% 4.06/1.72  tff(c_2464, plain, (![B_173, A_174]: (B_173=A_174 | k4_xboole_0(B_173, A_174)!=k1_xboole_0 | k4_xboole_0(A_174, B_173)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_2120])).
% 4.06/1.72  tff(c_2480, plain, (k1_tarski('#skF_5')='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_62, c_2464])).
% 4.06/1.72  tff(c_2499, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_2480])).
% 4.06/1.72  tff(c_2692, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2563, c_2499])).
% 4.06/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.72  tff(c_2733, plain, (~r2_hidden('#skF_5', '#skF_4') | r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2692, c_4])).
% 4.06/1.72  tff(c_2743, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_2733])).
% 4.06/1.72  tff(c_303, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_293])).
% 4.06/1.72  tff(c_2821, plain, (k1_tarski('#skF_5')='#skF_4' | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2743, c_303])).
% 4.06/1.72  tff(c_2837, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2821])).
% 4.06/1.72  tff(c_2839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2837])).
% 4.06/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.72  
% 4.06/1.72  Inference rules
% 4.06/1.72  ----------------------
% 4.06/1.72  #Ref     : 0
% 4.06/1.72  #Sup     : 647
% 4.06/1.72  #Fact    : 0
% 4.06/1.72  #Define  : 0
% 4.06/1.72  #Split   : 1
% 4.06/1.72  #Chain   : 0
% 4.06/1.72  #Close   : 0
% 4.06/1.72  
% 4.06/1.72  Ordering : KBO
% 4.06/1.72  
% 4.06/1.72  Simplification rules
% 4.06/1.72  ----------------------
% 4.06/1.72  #Subsume      : 108
% 4.06/1.72  #Demod        : 482
% 4.06/1.72  #Tautology    : 394
% 4.06/1.72  #SimpNegUnit  : 45
% 4.06/1.72  #BackRed      : 1
% 4.06/1.72  
% 4.06/1.72  #Partial instantiations: 0
% 4.06/1.72  #Strategies tried      : 1
% 4.06/1.72  
% 4.06/1.72  Timing (in seconds)
% 4.06/1.72  ----------------------
% 4.06/1.72  Preprocessing        : 0.33
% 4.06/1.72  Parsing              : 0.17
% 4.06/1.72  CNF conversion       : 0.03
% 4.06/1.72  Main loop            : 0.62
% 4.06/1.72  Inferencing          : 0.22
% 4.06/1.72  Reduction            : 0.23
% 4.06/1.72  Demodulation         : 0.17
% 4.06/1.72  BG Simplification    : 0.03
% 4.06/1.72  Subsumption          : 0.10
% 4.06/1.72  Abstraction          : 0.03
% 4.06/1.72  MUC search           : 0.00
% 4.06/1.72  Cooper               : 0.00
% 4.06/1.72  Total                : 0.99
% 4.06/1.72  Index Insertion      : 0.00
% 4.06/1.72  Index Deletion       : 0.00
% 4.06/1.72  Index Matching       : 0.00
% 4.06/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
