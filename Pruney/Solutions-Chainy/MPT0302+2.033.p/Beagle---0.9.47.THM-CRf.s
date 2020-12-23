%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 125 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 269 expanded)
%              Number of equality atoms :   22 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_18,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_3'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( r2_hidden(k4_tarski(A_31,B_32),k2_zfmisc_1(C_33,D_34))
      | ~ r2_hidden(B_32,D_34)
      | ~ r2_hidden(A_31,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [A_11,C_12,B_13,D_14] :
      ( r2_hidden(A_11,C_12)
      | ~ r2_hidden(k4_tarski(A_11,B_13),k2_zfmisc_1(C_12,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_33,plain,(
    ! [A_11,B_13] :
      ( r2_hidden(A_11,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_11,B_13),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_76,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,'#skF_5')
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_33])).

tff(c_159,plain,(
    ! [B_41] : ~ r2_hidden(B_41,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_173])).

tff(c_181,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_5')
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43,'#skF_5'),'#skF_5')
      | A_43 = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_43,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_199,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_195])).

tff(c_206,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_18,c_199])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [B_15,D_16,A_17,C_18] :
      ( r2_hidden(B_15,D_16)
      | ~ r2_hidden(k4_tarski(A_17,B_15),k2_zfmisc_1(C_18,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    ! [B_15,A_17] :
      ( r2_hidden(B_15,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_17,B_15),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_75,plain,(
    ! [B_32,A_31] :
      ( r2_hidden(B_32,'#skF_4')
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_37])).

tff(c_98,plain,(
    ! [A_37] : ~ r2_hidden(A_37,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_112])).

tff(c_119,plain,(
    ! [B_32] :
      ( r2_hidden(B_32,'#skF_4')
      | ~ r2_hidden(B_32,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_229,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_119])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [A_31] :
      ( r2_hidden(A_31,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_231,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_229,c_2])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_231])).

tff(c_238,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_180,c_234])).

tff(c_244,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_250,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_244])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:22:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.22  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.82/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.22  
% 1.82/1.23  tff(f_55, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 1.82/1.23  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.82/1.23  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.82/1.23  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.82/1.23  tff(c_18, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.23  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.23  tff(c_20, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.23  tff(c_10, plain, (![A_4]: (r2_hidden('#skF_3'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.82/1.23  tff(c_57, plain, (![A_31, B_32, C_33, D_34]: (r2_hidden(k4_tarski(A_31, B_32), k2_zfmisc_1(C_33, D_34)) | ~r2_hidden(B_32, D_34) | ~r2_hidden(A_31, C_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.23  tff(c_24, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.23  tff(c_30, plain, (![A_11, C_12, B_13, D_14]: (r2_hidden(A_11, C_12) | ~r2_hidden(k4_tarski(A_11, B_13), k2_zfmisc_1(C_12, D_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.23  tff(c_33, plain, (![A_11, B_13]: (r2_hidden(A_11, '#skF_5') | ~r2_hidden(k4_tarski(A_11, B_13), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_30])).
% 1.82/1.23  tff(c_76, plain, (![A_31, B_32]: (r2_hidden(A_31, '#skF_5') | ~r2_hidden(B_32, '#skF_5') | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_33])).
% 1.82/1.23  tff(c_159, plain, (![B_41]: (~r2_hidden(B_41, '#skF_5'))), inference(splitLeft, [status(thm)], [c_76])).
% 1.82/1.23  tff(c_173, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_10, c_159])).
% 1.82/1.23  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_173])).
% 1.82/1.23  tff(c_181, plain, (![A_42]: (r2_hidden(A_42, '#skF_5') | ~r2_hidden(A_42, '#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 1.82/1.23  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.23  tff(c_195, plain, (![A_43]: (r2_hidden('#skF_1'(A_43, '#skF_5'), '#skF_5') | A_43='#skF_5' | ~r2_hidden('#skF_2'(A_43, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_181, c_4])).
% 1.82/1.23  tff(c_199, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_8, c_195])).
% 1.82/1.23  tff(c_206, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_18, c_18, c_199])).
% 1.82/1.23  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.23  tff(c_34, plain, (![B_15, D_16, A_17, C_18]: (r2_hidden(B_15, D_16) | ~r2_hidden(k4_tarski(A_17, B_15), k2_zfmisc_1(C_18, D_16)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.23  tff(c_37, plain, (![B_15, A_17]: (r2_hidden(B_15, '#skF_4') | ~r2_hidden(k4_tarski(A_17, B_15), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_34])).
% 1.82/1.23  tff(c_75, plain, (![B_32, A_31]: (r2_hidden(B_32, '#skF_4') | ~r2_hidden(B_32, '#skF_5') | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_37])).
% 1.82/1.23  tff(c_98, plain, (![A_37]: (~r2_hidden(A_37, '#skF_4'))), inference(splitLeft, [status(thm)], [c_75])).
% 1.82/1.23  tff(c_112, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_98])).
% 1.82/1.23  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_112])).
% 1.82/1.23  tff(c_119, plain, (![B_32]: (r2_hidden(B_32, '#skF_4') | ~r2_hidden(B_32, '#skF_5'))), inference(splitRight, [status(thm)], [c_75])).
% 1.82/1.23  tff(c_229, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_206, c_119])).
% 1.82/1.23  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.23  tff(c_180, plain, (![A_31]: (r2_hidden(A_31, '#skF_5') | ~r2_hidden(A_31, '#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 1.82/1.23  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.23  tff(c_231, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_229, c_2])).
% 1.82/1.23  tff(c_234, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_18, c_231])).
% 1.82/1.23  tff(c_238, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_180, c_234])).
% 1.82/1.23  tff(c_244, plain, (~r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6, c_238])).
% 1.82/1.23  tff(c_250, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_244])).
% 1.82/1.23  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_250])).
% 1.82/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  Inference rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Ref     : 0
% 1.82/1.23  #Sup     : 40
% 1.82/1.23  #Fact    : 0
% 1.82/1.23  #Define  : 0
% 1.82/1.23  #Split   : 2
% 1.82/1.23  #Chain   : 0
% 1.82/1.23  #Close   : 0
% 1.82/1.23  
% 1.82/1.23  Ordering : KBO
% 1.82/1.23  
% 1.82/1.23  Simplification rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Subsume      : 8
% 1.82/1.23  #Demod        : 2
% 1.82/1.23  #Tautology    : 13
% 1.82/1.23  #SimpNegUnit  : 11
% 1.82/1.23  #BackRed      : 2
% 1.82/1.23  
% 1.82/1.23  #Partial instantiations: 0
% 1.82/1.23  #Strategies tried      : 1
% 1.82/1.23  
% 1.82/1.23  Timing (in seconds)
% 1.82/1.23  ----------------------
% 1.82/1.23  Preprocessing        : 0.27
% 1.82/1.23  Parsing              : 0.15
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.19
% 1.82/1.23  Inferencing          : 0.08
% 1.82/1.23  Reduction            : 0.04
% 1.82/1.23  Demodulation         : 0.03
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.04
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.49
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
