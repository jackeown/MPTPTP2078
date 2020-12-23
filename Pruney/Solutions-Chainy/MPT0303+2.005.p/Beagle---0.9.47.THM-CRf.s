%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:51 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 203 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 412 expanded)
%              Number of equality atoms :   19 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_40,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r2_hidden('#skF_5'(A_12,B_13),A_12)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_201,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_hidden(k4_tarski(A_62,B_63),k2_zfmisc_1(C_64,D_65))
      | ~ r2_hidden(B_63,D_65)
      | ~ r2_hidden(A_62,C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    k2_zfmisc_1('#skF_7','#skF_7') = k2_zfmisc_1('#skF_6','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_76,plain,(
    ! [B_39,D_40,A_41,C_42] :
      ( r2_hidden(B_39,D_40)
      | ~ r2_hidden(k4_tarski(A_41,B_39),k2_zfmisc_1(C_42,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [B_39,A_41] :
      ( r2_hidden(B_39,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_41,B_39),k2_zfmisc_1('#skF_6','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_76])).

tff(c_221,plain,(
    ! [B_63,A_62] :
      ( r2_hidden(B_63,'#skF_7')
      | ~ r2_hidden(B_63,'#skF_6')
      | ~ r2_hidden(A_62,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_201,c_79])).

tff(c_228,plain,(
    ! [A_68] : ~ r2_hidden(A_68,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_253,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_4'('#skF_6',B_13),B_13)
      | B_13 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_32,c_228])).

tff(c_227,plain,(
    ! [A_62] : ~ r2_hidden(A_62,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_309,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(k4_tarski(A_78,B_79),k2_zfmisc_1('#skF_6','#skF_6'))
      | ~ r2_hidden(B_79,'#skF_7')
      | ~ r2_hidden(A_78,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_201])).

tff(c_36,plain,(
    ! [B_16,D_18,A_15,C_17] :
      ( r2_hidden(B_16,D_18)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_315,plain,(
    ! [B_79,A_78] :
      ( r2_hidden(B_79,'#skF_6')
      | ~ r2_hidden(B_79,'#skF_7')
      | ~ r2_hidden(A_78,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_309,c_36])).

tff(c_327,plain,(
    ! [B_79,A_78] :
      ( ~ r2_hidden(B_79,'#skF_7')
      | ~ r2_hidden(A_78,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_315])).

tff(c_336,plain,(
    ! [A_80] : ~ r2_hidden(A_80,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_340,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_253,c_336])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_340])).

tff(c_370,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_374,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_253,c_370])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_374])).

tff(c_402,plain,(
    ! [B_82] :
      ( r2_hidden(B_82,'#skF_7')
      | ~ r2_hidden(B_82,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | ~ r2_hidden('#skF_5'(A_12,B_13),B_13)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1556,plain,(
    ! [A_164] :
      ( r2_hidden('#skF_4'(A_164,'#skF_7'),'#skF_7')
      | A_164 = '#skF_7'
      | ~ r2_hidden('#skF_5'(A_164,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_402,c_28])).

tff(c_1564,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_1556])).

tff(c_1569,plain,(
    r2_hidden('#skF_4'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_1564])).

tff(c_449,plain,(
    ! [A_89,B_90] :
      ( r2_hidden(k4_tarski(A_89,B_90),k2_zfmisc_1('#skF_6','#skF_6'))
      | ~ r2_hidden(B_90,'#skF_7')
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_201])).

tff(c_465,plain,(
    ! [B_90,A_89] :
      ( r2_hidden(B_90,'#skF_6')
      | ~ r2_hidden(B_90,'#skF_7')
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_449,c_36])).

tff(c_469,plain,(
    ! [A_89] : ~ r2_hidden(A_89,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_401,plain,(
    ! [B_63] :
      ( r2_hidden(B_63,'#skF_7')
      | ~ r2_hidden(B_63,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_501,plain,(
    ! [B_92] : ~ r2_hidden(B_92,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_401])).

tff(c_652,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_4'('#skF_6',B_108),B_108)
      | B_108 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_32,c_501])).

tff(c_660,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_652,c_469])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_660])).

tff(c_680,plain,(
    ! [B_90] :
      ( r2_hidden(B_90,'#skF_6')
      | ~ r2_hidden(B_90,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_1575,plain,(
    r2_hidden('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1569,c_680])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_4'(A_12,B_13),A_12)
      | r2_hidden('#skF_5'(A_12,B_13),A_12)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_4'(A_12,B_13),A_12)
      | ~ r2_hidden('#skF_5'(A_12,B_13),B_13)
      | B_13 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1580,plain,
    ( ~ r2_hidden('#skF_5'('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1575,c_26])).

tff(c_1586,plain,(
    ~ r2_hidden('#skF_5'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1580])).

tff(c_1591,plain,(
    ~ r2_hidden('#skF_5'('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_401,c_1586])).

tff(c_1594,plain,
    ( ~ r2_hidden('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_1591])).

tff(c_1600,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1575,c_1594])).

tff(c_1602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.60  
% 2.96/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.61  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.96/1.61  
% 2.96/1.61  %Foreground sorts:
% 2.96/1.61  
% 2.96/1.61  
% 2.96/1.61  %Background operators:
% 2.96/1.61  
% 2.96/1.61  
% 2.96/1.61  %Foreground operators:
% 2.96/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.61  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.61  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.96/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.96/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.96/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.96/1.61  
% 2.96/1.62  tff(f_59, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 2.96/1.62  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.96/1.62  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.96/1.62  tff(c_40, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.62  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r2_hidden('#skF_5'(A_12, B_13), A_12) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.62  tff(c_201, plain, (![A_62, B_63, C_64, D_65]: (r2_hidden(k4_tarski(A_62, B_63), k2_zfmisc_1(C_64, D_65)) | ~r2_hidden(B_63, D_65) | ~r2_hidden(A_62, C_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.62  tff(c_42, plain, (k2_zfmisc_1('#skF_7', '#skF_7')=k2_zfmisc_1('#skF_6', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.62  tff(c_76, plain, (![B_39, D_40, A_41, C_42]: (r2_hidden(B_39, D_40) | ~r2_hidden(k4_tarski(A_41, B_39), k2_zfmisc_1(C_42, D_40)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.62  tff(c_79, plain, (![B_39, A_41]: (r2_hidden(B_39, '#skF_7') | ~r2_hidden(k4_tarski(A_41, B_39), k2_zfmisc_1('#skF_6', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_76])).
% 2.96/1.62  tff(c_221, plain, (![B_63, A_62]: (r2_hidden(B_63, '#skF_7') | ~r2_hidden(B_63, '#skF_6') | ~r2_hidden(A_62, '#skF_6'))), inference(resolution, [status(thm)], [c_201, c_79])).
% 2.96/1.62  tff(c_228, plain, (![A_68]: (~r2_hidden(A_68, '#skF_6'))), inference(splitLeft, [status(thm)], [c_221])).
% 2.96/1.62  tff(c_253, plain, (![B_13]: (r2_hidden('#skF_4'('#skF_6', B_13), B_13) | B_13='#skF_6')), inference(resolution, [status(thm)], [c_32, c_228])).
% 2.96/1.62  tff(c_227, plain, (![A_62]: (~r2_hidden(A_62, '#skF_6'))), inference(splitLeft, [status(thm)], [c_221])).
% 2.96/1.62  tff(c_309, plain, (![A_78, B_79]: (r2_hidden(k4_tarski(A_78, B_79), k2_zfmisc_1('#skF_6', '#skF_6')) | ~r2_hidden(B_79, '#skF_7') | ~r2_hidden(A_78, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_201])).
% 2.96/1.62  tff(c_36, plain, (![B_16, D_18, A_15, C_17]: (r2_hidden(B_16, D_18) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.62  tff(c_315, plain, (![B_79, A_78]: (r2_hidden(B_79, '#skF_6') | ~r2_hidden(B_79, '#skF_7') | ~r2_hidden(A_78, '#skF_7'))), inference(resolution, [status(thm)], [c_309, c_36])).
% 2.96/1.62  tff(c_327, plain, (![B_79, A_78]: (~r2_hidden(B_79, '#skF_7') | ~r2_hidden(A_78, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_227, c_315])).
% 2.96/1.62  tff(c_336, plain, (![A_80]: (~r2_hidden(A_80, '#skF_7'))), inference(splitLeft, [status(thm)], [c_327])).
% 2.96/1.62  tff(c_340, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_253, c_336])).
% 2.96/1.62  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_340])).
% 2.96/1.62  tff(c_370, plain, (![B_81]: (~r2_hidden(B_81, '#skF_7'))), inference(splitRight, [status(thm)], [c_327])).
% 2.96/1.62  tff(c_374, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_253, c_370])).
% 2.96/1.62  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_374])).
% 2.96/1.62  tff(c_402, plain, (![B_82]: (r2_hidden(B_82, '#skF_7') | ~r2_hidden(B_82, '#skF_6'))), inference(splitRight, [status(thm)], [c_221])).
% 2.96/1.62  tff(c_28, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | ~r2_hidden('#skF_5'(A_12, B_13), B_13) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.62  tff(c_1556, plain, (![A_164]: (r2_hidden('#skF_4'(A_164, '#skF_7'), '#skF_7') | A_164='#skF_7' | ~r2_hidden('#skF_5'(A_164, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_402, c_28])).
% 2.96/1.62  tff(c_1564, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_32, c_1556])).
% 2.96/1.62  tff(c_1569, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_1564])).
% 2.96/1.62  tff(c_449, plain, (![A_89, B_90]: (r2_hidden(k4_tarski(A_89, B_90), k2_zfmisc_1('#skF_6', '#skF_6')) | ~r2_hidden(B_90, '#skF_7') | ~r2_hidden(A_89, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_201])).
% 2.96/1.62  tff(c_465, plain, (![B_90, A_89]: (r2_hidden(B_90, '#skF_6') | ~r2_hidden(B_90, '#skF_7') | ~r2_hidden(A_89, '#skF_7'))), inference(resolution, [status(thm)], [c_449, c_36])).
% 2.96/1.62  tff(c_469, plain, (![A_89]: (~r2_hidden(A_89, '#skF_7'))), inference(splitLeft, [status(thm)], [c_465])).
% 2.96/1.62  tff(c_401, plain, (![B_63]: (r2_hidden(B_63, '#skF_7') | ~r2_hidden(B_63, '#skF_6'))), inference(splitRight, [status(thm)], [c_221])).
% 2.96/1.62  tff(c_501, plain, (![B_92]: (~r2_hidden(B_92, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_469, c_401])).
% 2.96/1.62  tff(c_652, plain, (![B_108]: (r2_hidden('#skF_4'('#skF_6', B_108), B_108) | B_108='#skF_6')), inference(resolution, [status(thm)], [c_32, c_501])).
% 2.96/1.62  tff(c_660, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_652, c_469])).
% 2.96/1.62  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_660])).
% 2.96/1.62  tff(c_680, plain, (![B_90]: (r2_hidden(B_90, '#skF_6') | ~r2_hidden(B_90, '#skF_7'))), inference(splitRight, [status(thm)], [c_465])).
% 2.96/1.62  tff(c_1575, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_1569, c_680])).
% 2.96/1.62  tff(c_30, plain, (![A_12, B_13]: (~r2_hidden('#skF_4'(A_12, B_13), A_12) | r2_hidden('#skF_5'(A_12, B_13), A_12) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.62  tff(c_26, plain, (![A_12, B_13]: (~r2_hidden('#skF_4'(A_12, B_13), A_12) | ~r2_hidden('#skF_5'(A_12, B_13), B_13) | B_13=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.62  tff(c_1580, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1575, c_26])).
% 2.96/1.62  tff(c_1586, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_1580])).
% 2.96/1.62  tff(c_1591, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_401, c_1586])).
% 2.96/1.62  tff(c_1594, plain, (~r2_hidden('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_30, c_1591])).
% 2.96/1.62  tff(c_1600, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1575, c_1594])).
% 2.96/1.62  tff(c_1602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1600])).
% 2.96/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.62  
% 2.96/1.62  Inference rules
% 2.96/1.62  ----------------------
% 2.96/1.62  #Ref     : 0
% 2.96/1.62  #Sup     : 309
% 2.96/1.62  #Fact    : 0
% 2.96/1.62  #Define  : 0
% 2.96/1.62  #Split   : 4
% 2.96/1.62  #Chain   : 0
% 2.96/1.62  #Close   : 0
% 2.96/1.62  
% 2.96/1.62  Ordering : KBO
% 2.96/1.62  
% 2.96/1.62  Simplification rules
% 2.96/1.62  ----------------------
% 2.96/1.62  #Subsume      : 36
% 2.96/1.62  #Demod        : 79
% 2.96/1.62  #Tautology    : 85
% 2.96/1.62  #SimpNegUnit  : 30
% 2.96/1.62  #BackRed      : 19
% 2.96/1.62  
% 2.96/1.62  #Partial instantiations: 0
% 2.96/1.62  #Strategies tried      : 1
% 2.96/1.62  
% 2.96/1.62  Timing (in seconds)
% 2.96/1.62  ----------------------
% 2.96/1.62  Preprocessing        : 0.28
% 2.96/1.62  Parsing              : 0.14
% 2.96/1.62  CNF conversion       : 0.02
% 2.96/1.62  Main loop            : 0.45
% 2.96/1.62  Inferencing          : 0.18
% 2.96/1.62  Reduction            : 0.11
% 2.96/1.62  Demodulation         : 0.07
% 2.96/1.62  BG Simplification    : 0.03
% 2.96/1.62  Subsumption          : 0.11
% 2.96/1.62  Abstraction          : 0.02
% 2.96/1.62  MUC search           : 0.00
% 2.96/1.62  Cooper               : 0.00
% 2.96/1.62  Total                : 0.76
% 2.96/1.62  Index Insertion      : 0.00
% 2.96/1.62  Index Deletion       : 0.00
% 2.96/1.62  Index Matching       : 0.00
% 2.96/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
