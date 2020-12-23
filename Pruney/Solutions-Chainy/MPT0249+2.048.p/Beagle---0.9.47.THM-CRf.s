%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 122 expanded)
%              Number of equality atoms :   40 (  94 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
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
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(c_52,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_142,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | r2_hidden(D_39,k2_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_149,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,'#skF_8')
      | r2_hidden(D_42,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_142])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [D_43] :
      ( D_43 = '#skF_6'
      | ~ r2_hidden(D_43,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_149,c_28])).

tff(c_158,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_161,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_158])).

tff(c_165,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_20])).

tff(c_168,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_165])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_195,plain,(
    ! [B_49,A_50] :
      ( k1_tarski(B_49) = A_50
      | k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,k1_tarski(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_387,plain,(
    ! [B_67,A_68] :
      ( k1_tarski(B_67) = A_68
      | k1_xboole_0 = A_68
      | k4_xboole_0(A_68,k1_tarski(B_67)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_400,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_387])).

tff(c_408,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_400])).

tff(c_40,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(k1_tarski(A_18),B_19) = B_19
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_534,plain,(
    ! [B_71] :
      ( k2_xboole_0('#skF_7',B_71) = B_71
      | ~ r2_hidden('#skF_6',B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_40])).

tff(c_562,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_168,c_534])).

tff(c_412,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_54])).

tff(c_584,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_412])).

tff(c_586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:19:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  
% 2.30/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.30/1.30  
% 2.30/1.30  %Foreground sorts:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Background operators:
% 2.30/1.30  
% 2.30/1.30  
% 2.30/1.30  %Foreground operators:
% 2.30/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.30/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.30/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.30/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.30/1.30  
% 2.47/1.31  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.47/1.31  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.47/1.31  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.47/1.31  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.47/1.31  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.47/1.31  tff(f_65, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.47/1.31  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.47/1.31  tff(c_52, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.31  tff(c_48, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.31  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.47/1.31  tff(c_54, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.31  tff(c_142, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | r2_hidden(D_39, k2_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.31  tff(c_149, plain, (![D_42]: (~r2_hidden(D_42, '#skF_8') | r2_hidden(D_42, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_54, c_142])).
% 2.47/1.31  tff(c_28, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.31  tff(c_154, plain, (![D_43]: (D_43='#skF_6' | ~r2_hidden(D_43, '#skF_8'))), inference(resolution, [status(thm)], [c_149, c_28])).
% 2.47/1.31  tff(c_158, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_154])).
% 2.47/1.31  tff(c_161, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_48, c_158])).
% 2.47/1.31  tff(c_165, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_161, c_20])).
% 2.47/1.31  tff(c_168, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_48, c_165])).
% 2.47/1.31  tff(c_50, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.31  tff(c_62, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k2_xboole_0(A_25, B_26))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.31  tff(c_69, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_54, c_62])).
% 2.47/1.31  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.31  tff(c_195, plain, (![B_49, A_50]: (k1_tarski(B_49)=A_50 | k1_xboole_0=A_50 | ~r1_tarski(A_50, k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.31  tff(c_387, plain, (![B_67, A_68]: (k1_tarski(B_67)=A_68 | k1_xboole_0=A_68 | k4_xboole_0(A_68, k1_tarski(B_67))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_195])).
% 2.47/1.31  tff(c_400, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_69, c_387])).
% 2.47/1.31  tff(c_408, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_50, c_400])).
% 2.47/1.31  tff(c_40, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), B_19)=B_19 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.31  tff(c_534, plain, (![B_71]: (k2_xboole_0('#skF_7', B_71)=B_71 | ~r2_hidden('#skF_6', B_71))), inference(superposition, [status(thm), theory('equality')], [c_408, c_40])).
% 2.47/1.31  tff(c_562, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_168, c_534])).
% 2.47/1.31  tff(c_412, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_54])).
% 2.47/1.31  tff(c_584, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_562, c_412])).
% 2.47/1.31  tff(c_586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_584])).
% 2.47/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.31  
% 2.47/1.31  Inference rules
% 2.47/1.31  ----------------------
% 2.47/1.31  #Ref     : 0
% 2.47/1.31  #Sup     : 126
% 2.47/1.31  #Fact    : 0
% 2.47/1.31  #Define  : 0
% 2.47/1.31  #Split   : 0
% 2.47/1.31  #Chain   : 0
% 2.47/1.31  #Close   : 0
% 2.47/1.31  
% 2.47/1.32  Ordering : KBO
% 2.47/1.32  
% 2.47/1.32  Simplification rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Subsume      : 14
% 2.47/1.32  #Demod        : 38
% 2.47/1.32  #Tautology    : 69
% 2.47/1.32  #SimpNegUnit  : 8
% 2.47/1.32  #BackRed      : 4
% 2.47/1.32  
% 2.47/1.32  #Partial instantiations: 0
% 2.47/1.32  #Strategies tried      : 1
% 2.47/1.32  
% 2.47/1.32  Timing (in seconds)
% 2.47/1.32  ----------------------
% 2.47/1.32  Preprocessing        : 0.30
% 2.47/1.32  Parsing              : 0.15
% 2.47/1.32  CNF conversion       : 0.02
% 2.47/1.32  Main loop            : 0.27
% 2.47/1.32  Inferencing          : 0.10
% 2.47/1.32  Reduction            : 0.08
% 2.47/1.32  Demodulation         : 0.06
% 2.47/1.32  BG Simplification    : 0.02
% 2.47/1.32  Subsumption          : 0.05
% 2.47/1.32  Abstraction          : 0.01
% 2.47/1.32  MUC search           : 0.00
% 2.47/1.32  Cooper               : 0.00
% 2.47/1.32  Total                : 0.60
% 2.47/1.32  Index Insertion      : 0.00
% 2.47/1.32  Index Deletion       : 0.00
% 2.47/1.32  Index Matching       : 0.00
% 2.47/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
