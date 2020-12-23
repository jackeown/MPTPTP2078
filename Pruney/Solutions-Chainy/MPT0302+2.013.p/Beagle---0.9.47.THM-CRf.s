%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 132 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 271 expanded)
%              Number of equality atoms :   16 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_408,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( r2_hidden(k4_tarski(A_83,B_84),k2_zfmisc_1(C_85,D_86))
      | ~ r2_hidden(B_84,D_86)
      | ~ r2_hidden(A_83,C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    ! [B_30,D_31,A_32,C_33] :
      ( r2_hidden(B_30,D_31)
      | ~ r2_hidden(k4_tarski(A_32,B_30),k2_zfmisc_1(C_33,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [B_30,A_32] :
      ( r2_hidden(B_30,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_32,B_30),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_83])).

tff(c_429,plain,(
    ! [B_84,A_83] :
      ( r2_hidden(B_84,'#skF_4')
      | ~ r2_hidden(B_84,'#skF_5')
      | ~ r2_hidden(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_408,c_86])).

tff(c_435,plain,(
    ! [A_87] : ~ r2_hidden(A_87,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_458,plain,(
    ! [B_88] : r1_tarski('#skF_4',B_88) ),
    inference(resolution,[status(thm)],[c_6,c_435])).

tff(c_34,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,(
    ! [A_48,C_49,B_50] :
      ( ~ r2_hidden(A_48,C_49)
      | ~ r2_hidden(A_48,B_50)
      | ~ r2_hidden(A_48,k5_xboole_0(B_50,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_51,A_52] :
      ( ~ r2_hidden(A_51,k1_xboole_0)
      | ~ r2_hidden(A_51,A_52)
      | ~ r2_hidden(A_51,A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_118])).

tff(c_136,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_53),A_54)
      | r1_tarski(k1_xboole_0,B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_173,plain,(
    ! [B_58] : r1_tarski(k1_xboole_0,B_58) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,(
    ! [B_58] :
      ( k1_xboole_0 = B_58
      | ~ r1_tarski(B_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_173,c_28])).

tff(c_465,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_458,c_176])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_465])).

tff(c_475,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,'#skF_4')
      | ~ r2_hidden(B_89,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_498,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_5',B_90),'#skF_4')
      | r1_tarski('#skF_5',B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_475])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_506,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_498,c_4])).

tff(c_508,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_506,c_28])).

tff(c_511,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_508])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    ! [A_34,C_35,B_36,D_37] :
      ( r2_hidden(A_34,C_35)
      | ~ r2_hidden(k4_tarski(A_34,B_36),k2_zfmisc_1(C_35,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [A_34,B_36] :
      ( r2_hidden(A_34,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_34,B_36),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_87])).

tff(c_428,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(A_83,'#skF_5')
      | ~ r2_hidden(B_84,'#skF_5')
      | ~ r2_hidden(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_408,c_90])).

tff(c_534,plain,(
    ! [B_93] : ~ r2_hidden(B_93,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_559,plain,(
    ! [B_94] : r1_tarski('#skF_5',B_94) ),
    inference(resolution,[status(thm)],[c_6,c_534])).

tff(c_566,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_559,c_176])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_566])).

tff(c_620,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,'#skF_5')
      | ~ r2_hidden(A_97,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_642,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_98,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_620,c_4])).

tff(c_654,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_642])).

tff(c_661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_511,c_511,c_654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.48/1.36  
% 2.48/1.36  %Foreground sorts:
% 2.48/1.36  
% 2.48/1.36  
% 2.48/1.36  %Background operators:
% 2.48/1.36  
% 2.48/1.36  
% 2.48/1.36  %Foreground operators:
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.36  
% 2.66/1.38  tff(f_69, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.66/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.38  tff(f_60, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.66/1.38  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.66/1.38  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.66/1.38  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.66/1.38  tff(c_42, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.38  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.38  tff(c_408, plain, (![A_83, B_84, C_85, D_86]: (r2_hidden(k4_tarski(A_83, B_84), k2_zfmisc_1(C_85, D_86)) | ~r2_hidden(B_84, D_86) | ~r2_hidden(A_83, C_85))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.38  tff(c_48, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.38  tff(c_83, plain, (![B_30, D_31, A_32, C_33]: (r2_hidden(B_30, D_31) | ~r2_hidden(k4_tarski(A_32, B_30), k2_zfmisc_1(C_33, D_31)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.38  tff(c_86, plain, (![B_30, A_32]: (r2_hidden(B_30, '#skF_4') | ~r2_hidden(k4_tarski(A_32, B_30), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_83])).
% 2.66/1.38  tff(c_429, plain, (![B_84, A_83]: (r2_hidden(B_84, '#skF_4') | ~r2_hidden(B_84, '#skF_5') | ~r2_hidden(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_408, c_86])).
% 2.66/1.38  tff(c_435, plain, (![A_87]: (~r2_hidden(A_87, '#skF_4'))), inference(splitLeft, [status(thm)], [c_429])).
% 2.66/1.38  tff(c_458, plain, (![B_88]: (r1_tarski('#skF_4', B_88))), inference(resolution, [status(thm)], [c_6, c_435])).
% 2.66/1.38  tff(c_34, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.38  tff(c_118, plain, (![A_48, C_49, B_50]: (~r2_hidden(A_48, C_49) | ~r2_hidden(A_48, B_50) | ~r2_hidden(A_48, k5_xboole_0(B_50, C_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.38  tff(c_131, plain, (![A_51, A_52]: (~r2_hidden(A_51, k1_xboole_0) | ~r2_hidden(A_51, A_52) | ~r2_hidden(A_51, A_52))), inference(superposition, [status(thm), theory('equality')], [c_34, c_118])).
% 2.66/1.38  tff(c_136, plain, (![B_53, A_54]: (~r2_hidden('#skF_1'(k1_xboole_0, B_53), A_54) | r1_tarski(k1_xboole_0, B_53))), inference(resolution, [status(thm)], [c_6, c_131])).
% 2.66/1.38  tff(c_173, plain, (![B_58]: (r1_tarski(k1_xboole_0, B_58))), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.66/1.38  tff(c_28, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.38  tff(c_176, plain, (![B_58]: (k1_xboole_0=B_58 | ~r1_tarski(B_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_173, c_28])).
% 2.66/1.38  tff(c_465, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_458, c_176])).
% 2.66/1.38  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_465])).
% 2.66/1.38  tff(c_475, plain, (![B_89]: (r2_hidden(B_89, '#skF_4') | ~r2_hidden(B_89, '#skF_5'))), inference(splitRight, [status(thm)], [c_429])).
% 2.66/1.38  tff(c_498, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_5', B_90), '#skF_4') | r1_tarski('#skF_5', B_90))), inference(resolution, [status(thm)], [c_6, c_475])).
% 2.66/1.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.38  tff(c_506, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_498, c_4])).
% 2.66/1.38  tff(c_508, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_506, c_28])).
% 2.66/1.38  tff(c_511, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_508])).
% 2.66/1.38  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.38  tff(c_87, plain, (![A_34, C_35, B_36, D_37]: (r2_hidden(A_34, C_35) | ~r2_hidden(k4_tarski(A_34, B_36), k2_zfmisc_1(C_35, D_37)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.38  tff(c_90, plain, (![A_34, B_36]: (r2_hidden(A_34, '#skF_5') | ~r2_hidden(k4_tarski(A_34, B_36), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_87])).
% 2.66/1.38  tff(c_428, plain, (![A_83, B_84]: (r2_hidden(A_83, '#skF_5') | ~r2_hidden(B_84, '#skF_5') | ~r2_hidden(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_408, c_90])).
% 2.66/1.38  tff(c_534, plain, (![B_93]: (~r2_hidden(B_93, '#skF_5'))), inference(splitLeft, [status(thm)], [c_428])).
% 2.66/1.38  tff(c_559, plain, (![B_94]: (r1_tarski('#skF_5', B_94))), inference(resolution, [status(thm)], [c_6, c_534])).
% 2.66/1.38  tff(c_566, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_559, c_176])).
% 2.66/1.38  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_566])).
% 2.66/1.38  tff(c_620, plain, (![A_97]: (r2_hidden(A_97, '#skF_5') | ~r2_hidden(A_97, '#skF_4'))), inference(splitRight, [status(thm)], [c_428])).
% 2.66/1.38  tff(c_642, plain, (![A_98]: (r1_tarski(A_98, '#skF_5') | ~r2_hidden('#skF_1'(A_98, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_620, c_4])).
% 2.66/1.38  tff(c_654, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_642])).
% 2.66/1.38  tff(c_661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_511, c_511, c_654])).
% 2.66/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  Inference rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Ref     : 0
% 2.66/1.38  #Sup     : 122
% 2.66/1.38  #Fact    : 0
% 2.66/1.38  #Define  : 0
% 2.66/1.38  #Split   : 3
% 2.66/1.38  #Chain   : 0
% 2.66/1.38  #Close   : 0
% 2.66/1.38  
% 2.66/1.38  Ordering : KBO
% 2.66/1.38  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 26
% 2.66/1.38  #Demod        : 15
% 2.66/1.38  #Tautology    : 37
% 2.66/1.38  #SimpNegUnit  : 8
% 2.66/1.38  #BackRed      : 3
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.38  Preprocessing        : 0.29
% 2.66/1.38  Parsing              : 0.15
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.31
% 2.66/1.38  Inferencing          : 0.13
% 2.66/1.38  Reduction            : 0.07
% 2.66/1.38  Demodulation         : 0.05
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.07
% 2.66/1.38  Abstraction          : 0.01
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.64
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
