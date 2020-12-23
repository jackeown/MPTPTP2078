%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   61 (  96 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 177 expanded)
%              Number of equality atoms :   17 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_36,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_215,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_2'(A_79,B_80),B_80)
      | r2_hidden('#skF_3'(A_79,B_80),A_79)
      | B_80 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden(A_25,B_26)
      | ~ r1_xboole_0(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    ! [A_25] : ~ r2_hidden(A_25,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_235,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_80),B_80)
      | k1_xboole_0 = B_80 ) ),
    inference(resolution,[status(thm)],[c_215,c_55])).

tff(c_250,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( r2_hidden(k4_tarski(A_82,B_83),k2_zfmisc_1(C_84,D_85))
      | ~ r2_hidden(B_83,D_85)
      | ~ r2_hidden(A_82,C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_124,plain,(
    ! [A_49,C_50,B_51,D_52] :
      ( r2_hidden(A_49,C_50)
      | ~ r2_hidden(k4_tarski(A_49,B_51),k2_zfmisc_1(C_50,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_127,plain,(
    ! [A_49,B_51] :
      ( r2_hidden(A_49,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_49,B_51),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_270,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(A_82,'#skF_5')
      | ~ r2_hidden(B_83,'#skF_5')
      | ~ r2_hidden(A_82,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_250,c_127])).

tff(c_277,plain,(
    ! [B_86] : ~ r2_hidden(B_86,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_281,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_235,c_277])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_281])).

tff(c_313,plain,(
    ! [A_87] :
      ( r2_hidden(A_87,'#skF_5')
      | ~ r2_hidden(A_87,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_356,plain,(
    ! [A_90] :
      ( r1_tarski(A_90,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_90,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_313,c_4])).

tff(c_366,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_356])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),B_12)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_336,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(k4_tarski(A_88,B_89),k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(B_89,'#skF_6')
      | ~ r2_hidden(A_88,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_250])).

tff(c_34,plain,(
    ! [A_17,C_19,B_18,D_20] :
      ( r2_hidden(A_17,C_19)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_353,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(A_88,'#skF_6')
      | ~ r2_hidden(B_89,'#skF_6')
      | ~ r2_hidden(A_88,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_336,c_34])).

tff(c_422,plain,(
    ! [B_98] : ~ r2_hidden(B_98,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_426,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_235,c_422])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_426])).

tff(c_458,plain,(
    ! [A_99] :
      ( r2_hidden(A_99,'#skF_6')
      | ~ r2_hidden(A_99,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_505,plain,(
    ! [A_100] :
      ( r2_hidden('#skF_4'(A_100,'#skF_5'),'#skF_6')
      | ~ r2_xboole_0(A_100,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_458])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_4'(A_11,B_12),A_11)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_518,plain,(
    ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_505,c_22])).

tff(c_521,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_518])).

tff(c_524,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_521])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.48/1.35  
% 2.48/1.37  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.48/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.48/1.37  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.48/1.37  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.48/1.37  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.48/1.37  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.48/1.37  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.48/1.37  tff(f_56, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.48/1.37  tff(c_36, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.37  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.37  tff(c_215, plain, (![A_79, B_80]: (r2_hidden('#skF_2'(A_79, B_80), B_80) | r2_hidden('#skF_3'(A_79, B_80), A_79) | B_80=A_79)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.48/1.37  tff(c_26, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.37  tff(c_50, plain, (![A_25, B_26]: (~r2_hidden(A_25, B_26) | ~r1_xboole_0(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.37  tff(c_55, plain, (![A_25]: (~r2_hidden(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_50])).
% 2.48/1.37  tff(c_235, plain, (![B_80]: (r2_hidden('#skF_2'(k1_xboole_0, B_80), B_80) | k1_xboole_0=B_80)), inference(resolution, [status(thm)], [c_215, c_55])).
% 2.48/1.37  tff(c_250, plain, (![A_82, B_83, C_84, D_85]: (r2_hidden(k4_tarski(A_82, B_83), k2_zfmisc_1(C_84, D_85)) | ~r2_hidden(B_83, D_85) | ~r2_hidden(A_82, C_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.48/1.37  tff(c_42, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.37  tff(c_124, plain, (![A_49, C_50, B_51, D_52]: (r2_hidden(A_49, C_50) | ~r2_hidden(k4_tarski(A_49, B_51), k2_zfmisc_1(C_50, D_52)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.48/1.37  tff(c_127, plain, (![A_49, B_51]: (r2_hidden(A_49, '#skF_5') | ~r2_hidden(k4_tarski(A_49, B_51), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_124])).
% 2.48/1.37  tff(c_270, plain, (![A_82, B_83]: (r2_hidden(A_82, '#skF_5') | ~r2_hidden(B_83, '#skF_5') | ~r2_hidden(A_82, '#skF_6'))), inference(resolution, [status(thm)], [c_250, c_127])).
% 2.48/1.37  tff(c_277, plain, (![B_86]: (~r2_hidden(B_86, '#skF_5'))), inference(splitLeft, [status(thm)], [c_270])).
% 2.48/1.37  tff(c_281, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_235, c_277])).
% 2.48/1.37  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_281])).
% 2.48/1.37  tff(c_313, plain, (![A_87]: (r2_hidden(A_87, '#skF_5') | ~r2_hidden(A_87, '#skF_6'))), inference(splitRight, [status(thm)], [c_270])).
% 2.48/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.37  tff(c_356, plain, (![A_90]: (r1_tarski(A_90, '#skF_5') | ~r2_hidden('#skF_1'(A_90, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_313, c_4])).
% 2.48/1.37  tff(c_366, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_356])).
% 2.48/1.37  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.37  tff(c_24, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), B_12) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.37  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.37  tff(c_336, plain, (![A_88, B_89]: (r2_hidden(k4_tarski(A_88, B_89), k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(B_89, '#skF_6') | ~r2_hidden(A_88, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_250])).
% 2.48/1.37  tff(c_34, plain, (![A_17, C_19, B_18, D_20]: (r2_hidden(A_17, C_19) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.48/1.37  tff(c_353, plain, (![A_88, B_89]: (r2_hidden(A_88, '#skF_6') | ~r2_hidden(B_89, '#skF_6') | ~r2_hidden(A_88, '#skF_5'))), inference(resolution, [status(thm)], [c_336, c_34])).
% 2.48/1.37  tff(c_422, plain, (![B_98]: (~r2_hidden(B_98, '#skF_6'))), inference(splitLeft, [status(thm)], [c_353])).
% 2.48/1.37  tff(c_426, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_235, c_422])).
% 2.48/1.37  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_426])).
% 2.48/1.37  tff(c_458, plain, (![A_99]: (r2_hidden(A_99, '#skF_6') | ~r2_hidden(A_99, '#skF_5'))), inference(splitRight, [status(thm)], [c_353])).
% 2.48/1.37  tff(c_505, plain, (![A_100]: (r2_hidden('#skF_4'(A_100, '#skF_5'), '#skF_6') | ~r2_xboole_0(A_100, '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_458])).
% 2.48/1.37  tff(c_22, plain, (![A_11, B_12]: (~r2_hidden('#skF_4'(A_11, B_12), A_11) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.37  tff(c_518, plain, (~r2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_505, c_22])).
% 2.48/1.37  tff(c_521, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_518])).
% 2.48/1.37  tff(c_524, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_521])).
% 2.48/1.37  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_524])).
% 2.48/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.37  
% 2.48/1.37  Inference rules
% 2.48/1.37  ----------------------
% 2.48/1.37  #Ref     : 0
% 2.48/1.37  #Sup     : 95
% 2.48/1.37  #Fact    : 0
% 2.48/1.37  #Define  : 0
% 2.48/1.37  #Split   : 2
% 2.48/1.37  #Chain   : 0
% 2.48/1.37  #Close   : 0
% 2.48/1.37  
% 2.48/1.37  Ordering : KBO
% 2.48/1.37  
% 2.48/1.37  Simplification rules
% 2.48/1.37  ----------------------
% 2.48/1.37  #Subsume      : 15
% 2.48/1.37  #Demod        : 5
% 2.48/1.37  #Tautology    : 19
% 2.48/1.37  #SimpNegUnit  : 8
% 2.48/1.37  #BackRed      : 2
% 2.48/1.37  
% 2.48/1.37  #Partial instantiations: 0
% 2.48/1.37  #Strategies tried      : 1
% 2.48/1.37  
% 2.48/1.37  Timing (in seconds)
% 2.48/1.37  ----------------------
% 2.67/1.37  Preprocessing        : 0.31
% 2.67/1.37  Parsing              : 0.16
% 2.67/1.37  CNF conversion       : 0.02
% 2.67/1.37  Main loop            : 0.29
% 2.67/1.37  Inferencing          : 0.12
% 2.67/1.37  Reduction            : 0.07
% 2.67/1.37  Demodulation         : 0.04
% 2.67/1.37  BG Simplification    : 0.02
% 2.67/1.37  Subsumption          : 0.07
% 2.67/1.37  Abstraction          : 0.01
% 2.67/1.37  MUC search           : 0.00
% 2.67/1.37  Cooper               : 0.00
% 2.67/1.37  Total                : 0.63
% 2.67/1.37  Index Insertion      : 0.00
% 2.67/1.37  Index Deletion       : 0.00
% 2.67/1.37  Index Matching       : 0.00
% 2.67/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
