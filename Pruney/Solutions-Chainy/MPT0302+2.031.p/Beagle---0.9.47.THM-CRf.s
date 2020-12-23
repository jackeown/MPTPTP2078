%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 203 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52))
      | ~ r2_hidden(B_50,D_52)
      | ~ r2_hidden(A_49,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ! [B_41,D_42,A_43,C_44] :
      ( r2_hidden(B_41,D_42)
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1(C_44,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_87,plain,(
    ! [B_41,A_43] :
      ( r2_hidden(B_41,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_84])).

tff(c_110,plain,(
    ! [B_50,A_49] :
      ( r2_hidden(B_50,'#skF_4')
      | ~ r2_hidden(B_50,'#skF_5')
      | ~ r2_hidden(A_49,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_87])).

tff(c_117,plain,(
    ! [A_53] : ~ r2_hidden(A_53,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_133,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_133])).

tff(c_142,plain,(
    ! [B_54] :
      ( r2_hidden(B_54,'#skF_4')
      | ~ r2_hidden(B_54,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_197,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_2'(A_61,'#skF_5'),'#skF_4')
      | ~ r2_xboole_0(A_61,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_205,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_197,c_14])).

tff(c_208,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_205])).

tff(c_211,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_208])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    ! [A_37,C_38,B_39,D_40] :
      ( r2_hidden(A_37,C_38)
      | ~ r2_hidden(k4_tarski(A_37,B_39),k2_zfmisc_1(C_38,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    ! [A_37,B_39] :
      ( r2_hidden(A_37,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_37,B_39),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_80])).

tff(c_111,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,'#skF_5')
      | ~ r2_hidden(B_50,'#skF_5')
      | ~ r2_hidden(A_49,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_83])).

tff(c_234,plain,(
    ! [B_65] : ~ r2_hidden(B_65,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_18,c_234])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_258])).

tff(c_283,plain,(
    ! [A_69] :
      ( r2_hidden(A_69,'#skF_5')
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_301,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_70,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_283,c_4])).

tff(c_313,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_301])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_211,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.24  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.05/1.24  
% 2.05/1.24  %Foreground sorts:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Background operators:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Foreground operators:
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.05/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.24  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.24  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.24  
% 2.05/1.25  tff(f_72, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.05/1.25  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.05/1.25  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.05/1.25  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.05/1.25  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.05/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.25  tff(c_26, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.05/1.25  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.25  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.25  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.05/1.25  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.25  tff(c_90, plain, (![A_49, B_50, C_51, D_52]: (r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)) | ~r2_hidden(B_50, D_52) | ~r2_hidden(A_49, C_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.25  tff(c_32, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.05/1.25  tff(c_84, plain, (![B_41, D_42, A_43, C_44]: (r2_hidden(B_41, D_42) | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1(C_44, D_42)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.25  tff(c_87, plain, (![B_41, A_43]: (r2_hidden(B_41, '#skF_4') | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_84])).
% 2.05/1.25  tff(c_110, plain, (![B_50, A_49]: (r2_hidden(B_50, '#skF_4') | ~r2_hidden(B_50, '#skF_5') | ~r2_hidden(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_87])).
% 2.05/1.25  tff(c_117, plain, (![A_53]: (~r2_hidden(A_53, '#skF_4'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.05/1.25  tff(c_133, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_117])).
% 2.05/1.25  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_133])).
% 2.05/1.25  tff(c_142, plain, (![B_54]: (r2_hidden(B_54, '#skF_4') | ~r2_hidden(B_54, '#skF_5'))), inference(splitRight, [status(thm)], [c_110])).
% 2.05/1.25  tff(c_197, plain, (![A_61]: (r2_hidden('#skF_2'(A_61, '#skF_5'), '#skF_4') | ~r2_xboole_0(A_61, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.05/1.25  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.25  tff(c_205, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_197, c_14])).
% 2.05/1.25  tff(c_208, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_205])).
% 2.05/1.25  tff(c_211, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_26, c_208])).
% 2.05/1.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.25  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.05/1.25  tff(c_80, plain, (![A_37, C_38, B_39, D_40]: (r2_hidden(A_37, C_38) | ~r2_hidden(k4_tarski(A_37, B_39), k2_zfmisc_1(C_38, D_40)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.25  tff(c_83, plain, (![A_37, B_39]: (r2_hidden(A_37, '#skF_5') | ~r2_hidden(k4_tarski(A_37, B_39), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_80])).
% 2.05/1.25  tff(c_111, plain, (![A_49, B_50]: (r2_hidden(A_49, '#skF_5') | ~r2_hidden(B_50, '#skF_5') | ~r2_hidden(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_83])).
% 2.05/1.25  tff(c_234, plain, (![B_65]: (~r2_hidden(B_65, '#skF_5'))), inference(splitLeft, [status(thm)], [c_111])).
% 2.05/1.25  tff(c_258, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_18, c_234])).
% 2.05/1.25  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_258])).
% 2.05/1.25  tff(c_283, plain, (![A_69]: (r2_hidden(A_69, '#skF_5') | ~r2_hidden(A_69, '#skF_4'))), inference(splitRight, [status(thm)], [c_111])).
% 2.05/1.25  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.25  tff(c_301, plain, (![A_70]: (r1_tarski(A_70, '#skF_5') | ~r2_hidden('#skF_1'(A_70, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_283, c_4])).
% 2.05/1.25  tff(c_313, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_301])).
% 2.05/1.25  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_211, c_313])).
% 2.05/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  Inference rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Ref     : 0
% 2.05/1.25  #Sup     : 56
% 2.05/1.25  #Fact    : 0
% 2.05/1.25  #Define  : 0
% 2.05/1.25  #Split   : 2
% 2.05/1.25  #Chain   : 0
% 2.05/1.25  #Close   : 0
% 2.05/1.25  
% 2.05/1.25  Ordering : KBO
% 2.05/1.25  
% 2.05/1.25  Simplification rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Subsume      : 4
% 2.05/1.25  #Demod        : 3
% 2.05/1.25  #Tautology    : 11
% 2.05/1.25  #SimpNegUnit  : 8
% 2.05/1.25  #BackRed      : 2
% 2.05/1.25  
% 2.05/1.25  #Partial instantiations: 0
% 2.05/1.25  #Strategies tried      : 1
% 2.05/1.25  
% 2.05/1.25  Timing (in seconds)
% 2.05/1.25  ----------------------
% 2.05/1.25  Preprocessing        : 0.28
% 2.05/1.25  Parsing              : 0.15
% 2.05/1.26  CNF conversion       : 0.02
% 2.05/1.26  Main loop            : 0.20
% 2.05/1.26  Inferencing          : 0.08
% 2.05/1.26  Reduction            : 0.05
% 2.05/1.26  Demodulation         : 0.03
% 2.05/1.26  BG Simplification    : 0.01
% 2.05/1.26  Subsumption          : 0.05
% 2.05/1.26  Abstraction          : 0.01
% 2.05/1.26  MUC search           : 0.00
% 2.05/1.26  Cooper               : 0.00
% 2.05/1.26  Total                : 0.51
% 2.05/1.26  Index Insertion      : 0.00
% 2.05/1.26  Index Deletion       : 0.00
% 2.05/1.26  Index Matching       : 0.00
% 2.05/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
