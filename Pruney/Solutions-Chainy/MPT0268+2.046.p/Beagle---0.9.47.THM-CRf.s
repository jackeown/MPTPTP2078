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
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 107 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_69,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [B_41,A_40] :
      ( r1_xboole_0(B_41,k1_tarski(A_40))
      | r2_hidden(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k4_xboole_0(B_60,C_61))
      | ~ r1_xboole_0(A_59,C_61)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_12,c_103])).

tff(c_128,plain,(
    ! [B_60,C_61] :
      ( k4_xboole_0(B_60,C_61) = B_60
      | ~ r1_xboole_0(B_60,C_61)
      | ~ r1_tarski(B_60,B_60) ) ),
    inference(resolution,[status(thm)],[c_124,c_108])).

tff(c_135,plain,(
    ! [B_62,C_63] :
      ( k4_xboole_0(B_62,C_63) = B_62
      | ~ r1_xboole_0(B_62,C_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_128])).

tff(c_196,plain,(
    ! [B_70,A_71] :
      ( k4_xboole_0(B_70,k1_tarski(A_71)) = B_70
      | r2_hidden(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_72,c_135])).

tff(c_30,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_102,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_211,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_102])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_211])).

tff(c_234,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_235,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_254,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_34])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | ~ r1_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [B_10,A_9] : r1_xboole_0(B_10,k4_xboole_0(A_9,B_10)) ),
    inference(resolution,[status(thm)],[c_14,c_51])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden(A_42,B_43)
      | ~ r1_xboole_0(k1_tarski(A_42),B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_42,A_9] : ~ r2_hidden(A_42,k4_xboole_0(A_9,k1_tarski(A_42))) ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_258,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_82])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_258])).

tff(c_273,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_274,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_319,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_36])).

tff(c_275,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(B_72,A_73)
      | ~ r1_xboole_0(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_278,plain,(
    ! [B_10,A_9] : r1_xboole_0(B_10,k4_xboole_0(A_9,B_10)) ),
    inference(resolution,[status(thm)],[c_14,c_275])).

tff(c_297,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden(A_80,B_81)
      | ~ r1_xboole_0(k1_tarski(A_80),B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_306,plain,(
    ! [A_80,A_9] : ~ r2_hidden(A_80,k4_xboole_0(A_9,k1_tarski(A_80))) ),
    inference(resolution,[status(thm)],[c_278,c_297])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_306])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.22  
% 2.00/1.22  %Foreground sorts:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Background operators:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Foreground operators:
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.22  
% 2.07/1.23  tff(f_71, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.07/1.23  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.07/1.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.07/1.23  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.23  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.07/1.23  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.07/1.23  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.07/1.23  tff(f_60, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.07/1.23  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.23  tff(c_50, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.07/1.23  tff(c_69, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.23  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.23  tff(c_72, plain, (![B_41, A_40]: (r1_xboole_0(B_41, k1_tarski(A_40)) | r2_hidden(A_40, B_41))), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.07/1.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.23  tff(c_124, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k4_xboole_0(B_60, C_61)) | ~r1_xboole_0(A_59, C_61) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.23  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.23  tff(c_103, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.23  tff(c_108, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_12, c_103])).
% 2.07/1.23  tff(c_128, plain, (![B_60, C_61]: (k4_xboole_0(B_60, C_61)=B_60 | ~r1_xboole_0(B_60, C_61) | ~r1_tarski(B_60, B_60))), inference(resolution, [status(thm)], [c_124, c_108])).
% 2.07/1.23  tff(c_135, plain, (![B_62, C_63]: (k4_xboole_0(B_62, C_63)=B_62 | ~r1_xboole_0(B_62, C_63))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_128])).
% 2.07/1.23  tff(c_196, plain, (![B_70, A_71]: (k4_xboole_0(B_70, k1_tarski(A_71))=B_70 | r2_hidden(A_71, B_70))), inference(resolution, [status(thm)], [c_72, c_135])).
% 2.07/1.23  tff(c_30, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.23  tff(c_102, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_30])).
% 2.07/1.23  tff(c_211, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_196, c_102])).
% 2.07/1.23  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_211])).
% 2.07/1.23  tff(c_234, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.07/1.23  tff(c_235, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.07/1.23  tff(c_34, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.23  tff(c_254, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_34])).
% 2.07/1.23  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.23  tff(c_51, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | ~r1_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.23  tff(c_54, plain, (![B_10, A_9]: (r1_xboole_0(B_10, k4_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_14, c_51])).
% 2.07/1.23  tff(c_73, plain, (![A_42, B_43]: (~r2_hidden(A_42, B_43) | ~r1_xboole_0(k1_tarski(A_42), B_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.23  tff(c_82, plain, (![A_42, A_9]: (~r2_hidden(A_42, k4_xboole_0(A_9, k1_tarski(A_42))))), inference(resolution, [status(thm)], [c_54, c_73])).
% 2.07/1.23  tff(c_258, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_254, c_82])).
% 2.07/1.23  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_258])).
% 2.07/1.23  tff(c_273, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.07/1.23  tff(c_274, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.07/1.23  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.23  tff(c_319, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_36])).
% 2.07/1.23  tff(c_275, plain, (![B_72, A_73]: (r1_xboole_0(B_72, A_73) | ~r1_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.23  tff(c_278, plain, (![B_10, A_9]: (r1_xboole_0(B_10, k4_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_14, c_275])).
% 2.07/1.23  tff(c_297, plain, (![A_80, B_81]: (~r2_hidden(A_80, B_81) | ~r1_xboole_0(k1_tarski(A_80), B_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.23  tff(c_306, plain, (![A_80, A_9]: (~r2_hidden(A_80, k4_xboole_0(A_9, k1_tarski(A_80))))), inference(resolution, [status(thm)], [c_278, c_297])).
% 2.07/1.23  tff(c_323, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_319, c_306])).
% 2.07/1.23  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_273, c_323])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 71
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 2
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 6
% 2.07/1.23  #Demod        : 17
% 2.07/1.23  #Tautology    : 33
% 2.07/1.23  #SimpNegUnit  : 1
% 2.07/1.23  #BackRed      : 0
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.24  Preprocessing        : 0.29
% 2.07/1.24  Parsing              : 0.15
% 2.07/1.24  CNF conversion       : 0.02
% 2.07/1.24  Main loop            : 0.17
% 2.07/1.24  Inferencing          : 0.07
% 2.07/1.24  Reduction            : 0.05
% 2.07/1.24  Demodulation         : 0.04
% 2.07/1.24  BG Simplification    : 0.01
% 2.07/1.24  Subsumption          : 0.03
% 2.07/1.24  Abstraction          : 0.01
% 2.07/1.24  MUC search           : 0.00
% 2.07/1.24  Cooper               : 0.00
% 2.07/1.24  Total                : 0.50
% 2.07/1.24  Index Insertion      : 0.00
% 2.07/1.24  Index Deletion       : 0.00
% 2.07/1.24  Index Matching       : 0.00
% 2.07/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
