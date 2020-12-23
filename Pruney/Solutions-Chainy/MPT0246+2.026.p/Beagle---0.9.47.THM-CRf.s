%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:03 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  84 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_180,plain,(
    ! [D_56,A_57,B_58] :
      ( r2_hidden(D_56,A_57)
      | ~ r2_hidden(D_56,k4_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_569,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_97,B_98)),A_97)
      | k4_xboole_0(A_97,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_180])).

tff(c_50,plain,(
    ! [C_29] :
      ( C_29 = '#skF_6'
      | ~ r2_hidden(C_29,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_622,plain,(
    ! [B_99] :
      ( '#skF_4'(k4_xboole_0('#skF_5',B_99)) = '#skF_6'
      | k4_xboole_0('#skF_5',B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_569,c_50])).

tff(c_634,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_6',k4_xboole_0('#skF_5',B_99))
      | k4_xboole_0('#skF_5',B_99) = k1_xboole_0
      | k4_xboole_0('#skF_5',B_99) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_26])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,(
    ! [D_61,B_62,A_63] :
      ( ~ r2_hidden(D_61,B_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3029,plain,(
    ! [A_187,A_188,B_189] :
      ( ~ r2_hidden('#skF_3'(A_187,k4_xboole_0(A_188,B_189)),B_189)
      | r1_xboole_0(A_187,k4_xboole_0(A_188,B_189)) ) ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_3087,plain,(
    ! [A_190,A_191] : r1_xboole_0(A_190,k4_xboole_0(A_191,A_190)) ),
    inference(resolution,[status(thm)],[c_24,c_3029])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | ~ r1_xboole_0(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3395,plain,(
    ! [A_194,A_195] : ~ r2_hidden(A_194,k4_xboole_0(A_195,k1_tarski(A_194))) ),
    inference(resolution,[status(thm)],[c_3087,c_42])).

tff(c_3426,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_634,c_3395])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_387,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(B_76) = A_77
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,k1_tarski(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_398,plain,(
    ! [B_76,A_14] :
      ( k1_tarski(B_76) = A_14
      | k1_xboole_0 = A_14
      | k4_xboole_0(A_14,k1_tarski(B_76)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_387])).

tff(c_3593,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3426,c_398])).

tff(c_3649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_54,c_3593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.75  
% 3.97/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 3.97/1.75  
% 3.97/1.75  %Foreground sorts:
% 3.97/1.75  
% 3.97/1.75  
% 3.97/1.75  %Background operators:
% 3.97/1.75  
% 3.97/1.75  
% 3.97/1.75  %Foreground operators:
% 3.97/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.97/1.75  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.97/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.97/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.97/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.97/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.97/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.75  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.97/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.97/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.97/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.75  
% 3.97/1.76  tff(f_101, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.97/1.76  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.97/1.76  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.97/1.76  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.97/1.76  tff(f_80, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.97/1.76  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.97/1.76  tff(f_86, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.97/1.76  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.97/1.76  tff(c_54, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.97/1.76  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.97/1.76  tff(c_180, plain, (![D_56, A_57, B_58]: (r2_hidden(D_56, A_57) | ~r2_hidden(D_56, k4_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.97/1.76  tff(c_569, plain, (![A_97, B_98]: (r2_hidden('#skF_4'(k4_xboole_0(A_97, B_98)), A_97) | k4_xboole_0(A_97, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_180])).
% 3.97/1.76  tff(c_50, plain, (![C_29]: (C_29='#skF_6' | ~r2_hidden(C_29, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.97/1.76  tff(c_622, plain, (![B_99]: ('#skF_4'(k4_xboole_0('#skF_5', B_99))='#skF_6' | k4_xboole_0('#skF_5', B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_569, c_50])).
% 3.97/1.76  tff(c_634, plain, (![B_99]: (r2_hidden('#skF_6', k4_xboole_0('#skF_5', B_99)) | k4_xboole_0('#skF_5', B_99)=k1_xboole_0 | k4_xboole_0('#skF_5', B_99)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_622, c_26])).
% 3.97/1.76  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.97/1.76  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.97/1.76  tff(c_203, plain, (![D_61, B_62, A_63]: (~r2_hidden(D_61, B_62) | ~r2_hidden(D_61, k4_xboole_0(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.97/1.76  tff(c_3029, plain, (![A_187, A_188, B_189]: (~r2_hidden('#skF_3'(A_187, k4_xboole_0(A_188, B_189)), B_189) | r1_xboole_0(A_187, k4_xboole_0(A_188, B_189)))), inference(resolution, [status(thm)], [c_22, c_203])).
% 3.97/1.76  tff(c_3087, plain, (![A_190, A_191]: (r1_xboole_0(A_190, k4_xboole_0(A_191, A_190)))), inference(resolution, [status(thm)], [c_24, c_3029])).
% 3.97/1.76  tff(c_42, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | ~r1_xboole_0(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.97/1.76  tff(c_3395, plain, (![A_194, A_195]: (~r2_hidden(A_194, k4_xboole_0(A_195, k1_tarski(A_194))))), inference(resolution, [status(thm)], [c_3087, c_42])).
% 3.97/1.76  tff(c_3426, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_634, c_3395])).
% 3.97/1.76  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.97/1.76  tff(c_387, plain, (![B_76, A_77]: (k1_tarski(B_76)=A_77 | k1_xboole_0=A_77 | ~r1_tarski(A_77, k1_tarski(B_76)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.76  tff(c_398, plain, (![B_76, A_14]: (k1_tarski(B_76)=A_14 | k1_xboole_0=A_14 | k4_xboole_0(A_14, k1_tarski(B_76))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_387])).
% 3.97/1.76  tff(c_3593, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3426, c_398])).
% 3.97/1.76  tff(c_3649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_54, c_3593])).
% 3.97/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.76  
% 3.97/1.76  Inference rules
% 3.97/1.76  ----------------------
% 3.97/1.76  #Ref     : 0
% 3.97/1.76  #Sup     : 854
% 3.97/1.76  #Fact    : 0
% 3.97/1.76  #Define  : 0
% 3.97/1.76  #Split   : 2
% 3.97/1.76  #Chain   : 0
% 3.97/1.76  #Close   : 0
% 3.97/1.76  
% 3.97/1.76  Ordering : KBO
% 3.97/1.76  
% 3.97/1.76  Simplification rules
% 3.97/1.76  ----------------------
% 3.97/1.76  #Subsume      : 179
% 3.97/1.76  #Demod        : 465
% 3.97/1.76  #Tautology    : 408
% 3.97/1.76  #SimpNegUnit  : 101
% 3.97/1.76  #BackRed      : 1
% 3.97/1.76  
% 3.97/1.76  #Partial instantiations: 0
% 3.97/1.76  #Strategies tried      : 1
% 3.97/1.76  
% 3.97/1.76  Timing (in seconds)
% 3.97/1.76  ----------------------
% 3.97/1.76  Preprocessing        : 0.31
% 3.97/1.76  Parsing              : 0.16
% 3.97/1.76  CNF conversion       : 0.02
% 3.97/1.76  Main loop            : 0.68
% 3.97/1.76  Inferencing          : 0.23
% 3.97/1.76  Reduction            : 0.21
% 3.97/1.76  Demodulation         : 0.14
% 3.97/1.77  BG Simplification    : 0.03
% 3.97/1.77  Subsumption          : 0.16
% 3.97/1.77  Abstraction          : 0.03
% 3.97/1.77  MUC search           : 0.00
% 3.97/1.77  Cooper               : 0.00
% 3.97/1.77  Total                : 1.02
% 3.97/1.77  Index Insertion      : 0.00
% 3.97/1.77  Index Deletion       : 0.00
% 3.97/1.77  Index Matching       : 0.00
% 3.97/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
