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
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 (  92 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_115,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(k1_tarski(A_42),B_43) = k1_xboole_0
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_115,c_18])).

tff(c_44,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_160,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_676,plain,(
    ! [B_726,A_727] :
      ( B_726 = A_727
      | ~ r1_tarski(B_726,A_727)
      | k4_xboole_0(A_727,B_726) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_881,plain,(
    ! [B_875,A_876] :
      ( B_875 = A_876
      | k4_xboole_0(B_875,A_876) != k1_xboole_0
      | k4_xboole_0(A_876,B_875) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_676])).

tff(c_890,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_881])).

tff(c_899,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_890])).

tff(c_912,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_899])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_173,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_696,plain,(
    ! [A_751,B_752] :
      ( r2_hidden('#skF_2'(A_751),B_752)
      | ~ r1_tarski(A_751,B_752)
      | k1_xboole_0 = A_751 ) ),
    inference(resolution,[status(thm)],[c_8,c_173])).

tff(c_22,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_709,plain,(
    ! [A_776,A_777] :
      ( A_776 = '#skF_2'(A_777)
      | ~ r1_tarski(A_777,k1_tarski(A_776))
      | k1_xboole_0 = A_777 ) ),
    inference(resolution,[status(thm)],[c_696,c_22])).

tff(c_989,plain,(
    ! [A_994,A_995] :
      ( A_994 = '#skF_2'(A_995)
      | k1_xboole_0 = A_995
      | k4_xboole_0(A_995,k1_tarski(A_994)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_709])).

tff(c_1009,plain,
    ( '#skF_2'('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_989])).

tff(c_1015,plain,(
    '#skF_2'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1009])).

tff(c_1022,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_8])).

tff(c_1027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_912,c_1022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:49:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 2.50/1.38  
% 2.50/1.38  %Foreground sorts:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Background operators:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Foreground operators:
% 2.50/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.50/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.50/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.50/1.38  
% 2.50/1.39  tff(f_79, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.50/1.39  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.50/1.39  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.50/1.39  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.39  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.50/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.50/1.39  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.50/1.39  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.50/1.39  tff(c_115, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.50/1.39  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.39  tff(c_122, plain, (![A_42, B_43]: (k4_xboole_0(k1_tarski(A_42), B_43)=k1_xboole_0 | ~r2_hidden(A_42, B_43))), inference(resolution, [status(thm)], [c_115, c_18])).
% 2.50/1.39  tff(c_44, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.50/1.39  tff(c_48, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.50/1.39  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.39  tff(c_160, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.39  tff(c_676, plain, (![B_726, A_727]: (B_726=A_727 | ~r1_tarski(B_726, A_727) | k4_xboole_0(A_727, B_726)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_160])).
% 2.50/1.39  tff(c_881, plain, (![B_875, A_876]: (B_875=A_876 | k4_xboole_0(B_875, A_876)!=k1_xboole_0 | k4_xboole_0(A_876, B_875)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_676])).
% 2.50/1.39  tff(c_890, plain, (k1_tarski('#skF_6')='#skF_5' | k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_48, c_881])).
% 2.50/1.39  tff(c_899, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_890])).
% 2.50/1.39  tff(c_912, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_122, c_899])).
% 2.50/1.39  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.50/1.39  tff(c_173, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.39  tff(c_696, plain, (![A_751, B_752]: (r2_hidden('#skF_2'(A_751), B_752) | ~r1_tarski(A_751, B_752) | k1_xboole_0=A_751)), inference(resolution, [status(thm)], [c_8, c_173])).
% 2.50/1.39  tff(c_22, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.39  tff(c_709, plain, (![A_776, A_777]: (A_776='#skF_2'(A_777) | ~r1_tarski(A_777, k1_tarski(A_776)) | k1_xboole_0=A_777)), inference(resolution, [status(thm)], [c_696, c_22])).
% 2.50/1.39  tff(c_989, plain, (![A_994, A_995]: (A_994='#skF_2'(A_995) | k1_xboole_0=A_995 | k4_xboole_0(A_995, k1_tarski(A_994))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_709])).
% 2.50/1.39  tff(c_1009, plain, ('#skF_2'('#skF_5')='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_48, c_989])).
% 2.50/1.39  tff(c_1015, plain, ('#skF_2'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_46, c_1009])).
% 2.50/1.39  tff(c_1022, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1015, c_8])).
% 2.50/1.39  tff(c_1027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_912, c_1022])).
% 2.50/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.39  
% 2.50/1.39  Inference rules
% 2.50/1.39  ----------------------
% 2.50/1.39  #Ref     : 0
% 2.50/1.39  #Sup     : 135
% 2.50/1.39  #Fact    : 0
% 2.50/1.39  #Define  : 0
% 2.50/1.39  #Split   : 0
% 2.50/1.39  #Chain   : 0
% 2.50/1.39  #Close   : 0
% 2.50/1.39  
% 2.50/1.39  Ordering : KBO
% 2.50/1.39  
% 2.50/1.39  Simplification rules
% 2.50/1.39  ----------------------
% 2.50/1.39  #Subsume      : 8
% 2.50/1.39  #Demod        : 14
% 2.50/1.39  #Tautology    : 53
% 2.50/1.39  #SimpNegUnit  : 6
% 2.50/1.39  #BackRed      : 0
% 2.50/1.39  
% 2.50/1.39  #Partial instantiations: 560
% 2.50/1.39  #Strategies tried      : 1
% 2.50/1.39  
% 2.50/1.39  Timing (in seconds)
% 2.50/1.39  ----------------------
% 2.50/1.39  Preprocessing        : 0.31
% 2.50/1.39  Parsing              : 0.16
% 2.50/1.39  CNF conversion       : 0.02
% 2.50/1.39  Main loop            : 0.33
% 2.50/1.39  Inferencing          : 0.17
% 2.50/1.39  Reduction            : 0.07
% 2.50/1.39  Demodulation         : 0.05
% 2.50/1.39  BG Simplification    : 0.02
% 2.50/1.39  Subsumption          : 0.05
% 2.50/1.39  Abstraction          : 0.01
% 2.50/1.39  MUC search           : 0.00
% 2.50/1.39  Cooper               : 0.00
% 2.50/1.39  Total                : 0.67
% 2.50/1.39  Index Insertion      : 0.00
% 2.50/1.40  Index Deletion       : 0.00
% 2.50/1.40  Index Matching       : 0.00
% 2.50/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
