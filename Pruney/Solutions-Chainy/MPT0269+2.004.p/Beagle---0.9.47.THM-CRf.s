%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_60,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_976,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,k1_tarski(B_96)) = A_95
      | r2_hidden(B_96,A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1009,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_64])).

tff(c_1046,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1009])).

tff(c_810,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2431,plain,(
    ! [A_161,B_162] :
      ( '#skF_1'(k1_tarski(A_161),B_162) = A_161
      | r1_tarski(k1_tarski(A_161),B_162) ) ),
    inference(resolution,[status(thm)],[c_810,c_38])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2453,plain,(
    ! [A_161,B_162] :
      ( k4_xboole_0(k1_tarski(A_161),B_162) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_161),B_162) = A_161 ) ),
    inference(resolution,[status(thm)],[c_2431,c_20])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1058,plain,(
    ! [B_97,A_98] :
      ( B_97 = A_98
      | ~ r1_tarski(B_97,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2551,plain,(
    ! [B_168,A_169] :
      ( B_168 = A_169
      | ~ r1_tarski(B_168,A_169)
      | k4_xboole_0(A_169,B_168) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_1058])).

tff(c_3485,plain,(
    ! [B_194,A_195] :
      ( B_194 = A_195
      | k4_xboole_0(B_194,A_195) != k1_xboole_0
      | k4_xboole_0(A_195,B_194) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_2551])).

tff(c_3505,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_3485])).

tff(c_3525,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3505])).

tff(c_3534,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2453,c_3525])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3544,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3534,c_6])).

tff(c_3554,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_3544])).

tff(c_1070,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_1058])).

tff(c_3563,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3554,c_1070])).

tff(c_3579,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3563])).

tff(c_3581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.75  
% 3.78/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.75  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.78/1.75  
% 3.78/1.75  %Foreground sorts:
% 3.78/1.75  
% 3.78/1.75  
% 3.78/1.75  %Background operators:
% 3.78/1.75  
% 3.78/1.75  
% 3.78/1.75  %Foreground operators:
% 3.78/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.78/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.78/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.78/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.78/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.78/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.78/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.78/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.75  
% 3.78/1.76  tff(f_92, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.78/1.76  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.78/1.76  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.78/1.76  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.78/1.76  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.78/1.76  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.78/1.76  tff(c_60, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.78/1.76  tff(c_64, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.78/1.76  tff(c_62, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.78/1.76  tff(c_976, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k1_tarski(B_96))=A_95 | r2_hidden(B_96, A_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.78/1.76  tff(c_1009, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_976, c_64])).
% 3.78/1.76  tff(c_1046, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_1009])).
% 3.78/1.76  tff(c_810, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), A_88) | r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.76  tff(c_38, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.78/1.76  tff(c_2431, plain, (![A_161, B_162]: ('#skF_1'(k1_tarski(A_161), B_162)=A_161 | r1_tarski(k1_tarski(A_161), B_162))), inference(resolution, [status(thm)], [c_810, c_38])).
% 3.78/1.76  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.78/1.76  tff(c_2453, plain, (![A_161, B_162]: (k4_xboole_0(k1_tarski(A_161), B_162)=k1_xboole_0 | '#skF_1'(k1_tarski(A_161), B_162)=A_161)), inference(resolution, [status(thm)], [c_2431, c_20])).
% 3.78/1.76  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.78/1.76  tff(c_1058, plain, (![B_97, A_98]: (B_97=A_98 | ~r1_tarski(B_97, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.78/1.76  tff(c_2551, plain, (![B_168, A_169]: (B_168=A_169 | ~r1_tarski(B_168, A_169) | k4_xboole_0(A_169, B_168)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1058])).
% 3.78/1.76  tff(c_3485, plain, (![B_194, A_195]: (B_194=A_195 | k4_xboole_0(B_194, A_195)!=k1_xboole_0 | k4_xboole_0(A_195, B_194)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_2551])).
% 3.78/1.76  tff(c_3505, plain, (k1_tarski('#skF_5')='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_64, c_3485])).
% 3.78/1.76  tff(c_3525, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_3505])).
% 3.78/1.76  tff(c_3534, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2453, c_3525])).
% 3.78/1.76  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.76  tff(c_3544, plain, (~r2_hidden('#skF_5', '#skF_4') | r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3534, c_6])).
% 3.78/1.76  tff(c_3554, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_3544])).
% 3.78/1.76  tff(c_1070, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1058])).
% 3.78/1.76  tff(c_3563, plain, (k1_tarski('#skF_5')='#skF_4' | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_3554, c_1070])).
% 3.78/1.76  tff(c_3579, plain, (k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3563])).
% 3.78/1.76  tff(c_3581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3579])).
% 3.78/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.76  
% 3.78/1.76  Inference rules
% 3.78/1.76  ----------------------
% 3.78/1.76  #Ref     : 0
% 3.78/1.76  #Sup     : 822
% 3.78/1.76  #Fact    : 0
% 3.78/1.76  #Define  : 0
% 3.78/1.76  #Split   : 0
% 3.78/1.76  #Chain   : 0
% 3.78/1.76  #Close   : 0
% 3.78/1.76  
% 3.78/1.76  Ordering : KBO
% 3.78/1.76  
% 3.78/1.76  Simplification rules
% 3.78/1.76  ----------------------
% 3.78/1.76  #Subsume      : 119
% 3.78/1.76  #Demod        : 686
% 3.78/1.76  #Tautology    : 555
% 3.78/1.76  #SimpNegUnit  : 41
% 3.78/1.76  #BackRed      : 5
% 3.78/1.76  
% 3.78/1.76  #Partial instantiations: 0
% 3.78/1.76  #Strategies tried      : 1
% 3.78/1.76  
% 3.78/1.76  Timing (in seconds)
% 3.78/1.76  ----------------------
% 3.78/1.76  Preprocessing        : 0.32
% 3.78/1.76  Parsing              : 0.17
% 3.78/1.76  CNF conversion       : 0.02
% 3.78/1.76  Main loop            : 0.64
% 3.78/1.76  Inferencing          : 0.23
% 3.78/1.76  Reduction            : 0.25
% 3.78/1.76  Demodulation         : 0.19
% 3.78/1.76  BG Simplification    : 0.03
% 3.78/1.76  Subsumption          : 0.10
% 3.78/1.76  Abstraction          : 0.03
% 3.78/1.76  MUC search           : 0.00
% 3.78/1.76  Cooper               : 0.00
% 3.78/1.76  Total                : 0.99
% 3.78/1.76  Index Insertion      : 0.00
% 3.78/1.76  Index Deletion       : 0.00
% 3.78/1.76  Index Matching       : 0.00
% 3.78/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
