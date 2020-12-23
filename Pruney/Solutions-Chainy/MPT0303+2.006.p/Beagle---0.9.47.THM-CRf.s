%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:51 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 165 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 332 expanded)
%              Number of equality atoms :   12 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_24,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47))
      | ~ r2_hidden(B_45,D_47)
      | ~ r2_hidden(A_44,C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    k2_zfmisc_1('#skF_3','#skF_3') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    ! [B_36,D_37,A_38,C_39] :
      ( r2_hidden(B_36,D_37)
      | ~ r2_hidden(k4_tarski(A_38,B_36),k2_zfmisc_1(C_39,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [B_36,A_38] :
      ( r2_hidden(B_36,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_38,B_36),k2_zfmisc_1('#skF_4','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_96,plain,(
    ! [B_45,A_44] :
      ( r2_hidden(B_45,'#skF_3')
      | ~ r2_hidden(B_45,'#skF_4')
      | ~ r2_hidden(A_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_73])).

tff(c_101,plain,(
    ! [A_44] : ~ r2_hidden(A_44,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_119,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(k4_tarski(A_50,B_51),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_51,'#skF_3')
      | ~ r2_hidden(A_50,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_22,plain,(
    ! [A_11,C_13,B_12,D_14] :
      ( r2_hidden(A_11,C_13)
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,'#skF_4')
      | ~ r2_hidden(B_51,'#skF_3')
      | ~ r2_hidden(A_50,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_119,c_22])).

tff(c_141,plain,(
    ! [B_51,A_50] :
      ( ~ r2_hidden(B_51,'#skF_3')
      | ~ r2_hidden(A_50,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_131])).

tff(c_160,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_183,plain,(
    ! [B_58] : r1_tarski('#skF_3',B_58) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

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

tff(c_102,plain,(
    ! [A_48] : ~ r2_hidden(A_48,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_113,plain,(
    ! [A_49] : ~ r2_xboole_0(A_49,'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_118,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_187,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_183,c_118])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_187])).

tff(c_195,plain,(
    ! [B_59] : ~ r2_hidden(B_59,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_218,plain,(
    ! [B_63] : r1_tarski('#skF_3',B_63) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_222,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_218,c_118])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_222])).

tff(c_228,plain,(
    ! [B_64] :
      ( r2_hidden(B_64,'#skF_3')
      | ~ r2_hidden(B_64,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_263,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_69,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_228,c_4])).

tff(c_273,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_263])).

tff(c_275,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(k4_tarski(A_71,B_72),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_72,'#skF_3')
      | ~ r2_hidden(A_71,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_20,plain,(
    ! [B_12,D_14,A_11,C_13] :
      ( r2_hidden(B_12,D_14)
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_292,plain,(
    ! [B_72,A_71] :
      ( r2_hidden(B_72,'#skF_4')
      | ~ r2_hidden(B_72,'#skF_3')
      | ~ r2_hidden(A_71,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_275,c_20])).

tff(c_299,plain,(
    ! [A_73] : ~ r2_hidden(A_73,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_314,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_299])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_242,plain,(
    ! [B_65] :
      ( ~ r2_xboole_0('#skF_3',B_65)
      | ~ r2_hidden('#skF_2'('#skF_3',B_65),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_228,c_14])).

tff(c_247,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_242])).

tff(c_250,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_247])).

tff(c_253,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_250])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_253])).

tff(c_347,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,'#skF_4')
      | ~ r2_hidden(B_78,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_367,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_2'(A_79,'#skF_3'),'#skF_4')
      | ~ r2_xboole_0(A_79,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_347])).

tff(c_380,plain,(
    ~ r2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_367,c_14])).

tff(c_383,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_380])).

tff(c_386,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_383])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.03/1.27  
% 2.03/1.27  %Foreground sorts:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Background operators:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Foreground operators:
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.27  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.27  
% 2.03/1.28  tff(f_60, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 2.03/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.28  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.03/1.28  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.03/1.28  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.03/1.28  tff(c_24, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.28  tff(c_76, plain, (![A_44, B_45, C_46, D_47]: (r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)) | ~r2_hidden(B_45, D_47) | ~r2_hidden(A_44, C_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.28  tff(c_26, plain, (k2_zfmisc_1('#skF_3', '#skF_3')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.28  tff(c_70, plain, (![B_36, D_37, A_38, C_39]: (r2_hidden(B_36, D_37) | ~r2_hidden(k4_tarski(A_38, B_36), k2_zfmisc_1(C_39, D_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.28  tff(c_73, plain, (![B_36, A_38]: (r2_hidden(B_36, '#skF_3') | ~r2_hidden(k4_tarski(A_38, B_36), k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_70])).
% 2.03/1.28  tff(c_96, plain, (![B_45, A_44]: (r2_hidden(B_45, '#skF_3') | ~r2_hidden(B_45, '#skF_4') | ~r2_hidden(A_44, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_73])).
% 2.03/1.28  tff(c_101, plain, (![A_44]: (~r2_hidden(A_44, '#skF_4'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.03/1.28  tff(c_119, plain, (![A_50, B_51]: (r2_hidden(k4_tarski(A_50, B_51), k2_zfmisc_1('#skF_4', '#skF_4')) | ~r2_hidden(B_51, '#skF_3') | ~r2_hidden(A_50, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_76])).
% 2.03/1.28  tff(c_22, plain, (![A_11, C_13, B_12, D_14]: (r2_hidden(A_11, C_13) | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.28  tff(c_131, plain, (![A_50, B_51]: (r2_hidden(A_50, '#skF_4') | ~r2_hidden(B_51, '#skF_3') | ~r2_hidden(A_50, '#skF_3'))), inference(resolution, [status(thm)], [c_119, c_22])).
% 2.03/1.28  tff(c_141, plain, (![B_51, A_50]: (~r2_hidden(B_51, '#skF_3') | ~r2_hidden(A_50, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_101, c_131])).
% 2.03/1.28  tff(c_160, plain, (![A_54]: (~r2_hidden(A_54, '#skF_3'))), inference(splitLeft, [status(thm)], [c_141])).
% 2.03/1.28  tff(c_183, plain, (![B_58]: (r1_tarski('#skF_3', B_58))), inference(resolution, [status(thm)], [c_6, c_160])).
% 2.03/1.28  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.28  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.28  tff(c_102, plain, (![A_48]: (~r2_hidden(A_48, '#skF_4'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.03/1.28  tff(c_113, plain, (![A_49]: (~r2_xboole_0(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_102])).
% 2.03/1.28  tff(c_118, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_113])).
% 2.03/1.28  tff(c_187, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_183, c_118])).
% 2.03/1.28  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_187])).
% 2.03/1.28  tff(c_195, plain, (![B_59]: (~r2_hidden(B_59, '#skF_3'))), inference(splitRight, [status(thm)], [c_141])).
% 2.03/1.28  tff(c_218, plain, (![B_63]: (r1_tarski('#skF_3', B_63))), inference(resolution, [status(thm)], [c_6, c_195])).
% 2.03/1.28  tff(c_222, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_218, c_118])).
% 2.03/1.28  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_222])).
% 2.03/1.28  tff(c_228, plain, (![B_64]: (r2_hidden(B_64, '#skF_3') | ~r2_hidden(B_64, '#skF_4'))), inference(splitRight, [status(thm)], [c_96])).
% 2.03/1.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.28  tff(c_263, plain, (![A_69]: (r1_tarski(A_69, '#skF_3') | ~r2_hidden('#skF_1'(A_69, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_228, c_4])).
% 2.03/1.28  tff(c_273, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_263])).
% 2.03/1.28  tff(c_275, plain, (![A_71, B_72]: (r2_hidden(k4_tarski(A_71, B_72), k2_zfmisc_1('#skF_4', '#skF_4')) | ~r2_hidden(B_72, '#skF_3') | ~r2_hidden(A_71, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_76])).
% 2.03/1.28  tff(c_20, plain, (![B_12, D_14, A_11, C_13]: (r2_hidden(B_12, D_14) | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.28  tff(c_292, plain, (![B_72, A_71]: (r2_hidden(B_72, '#skF_4') | ~r2_hidden(B_72, '#skF_3') | ~r2_hidden(A_71, '#skF_3'))), inference(resolution, [status(thm)], [c_275, c_20])).
% 2.03/1.28  tff(c_299, plain, (![A_73]: (~r2_hidden(A_73, '#skF_3'))), inference(splitLeft, [status(thm)], [c_292])).
% 2.03/1.28  tff(c_314, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_299])).
% 2.03/1.28  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.28  tff(c_242, plain, (![B_65]: (~r2_xboole_0('#skF_3', B_65) | ~r2_hidden('#skF_2'('#skF_3', B_65), '#skF_4'))), inference(resolution, [status(thm)], [c_228, c_14])).
% 2.03/1.28  tff(c_247, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_242])).
% 2.03/1.28  tff(c_250, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_247])).
% 2.03/1.28  tff(c_253, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_24, c_250])).
% 2.03/1.28  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_253])).
% 2.03/1.28  tff(c_347, plain, (![B_78]: (r2_hidden(B_78, '#skF_4') | ~r2_hidden(B_78, '#skF_3'))), inference(splitRight, [status(thm)], [c_292])).
% 2.03/1.28  tff(c_367, plain, (![A_79]: (r2_hidden('#skF_2'(A_79, '#skF_3'), '#skF_4') | ~r2_xboole_0(A_79, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_347])).
% 2.03/1.28  tff(c_380, plain, (~r2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_367, c_14])).
% 2.03/1.28  tff(c_383, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_380])).
% 2.03/1.28  tff(c_386, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_383])).
% 2.03/1.28  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_386])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 66
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 3
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 12
% 2.03/1.28  #Demod        : 2
% 2.03/1.28  #Tautology    : 14
% 2.03/1.28  #SimpNegUnit  : 13
% 2.03/1.28  #BackRed      : 8
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.03/1.28  Preprocessing        : 0.28
% 2.03/1.28  Parsing              : 0.15
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.23
% 2.03/1.28  Inferencing          : 0.09
% 2.03/1.28  Reduction            : 0.06
% 2.03/1.28  Demodulation         : 0.03
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.28  Subsumption          : 0.05
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.29  Total                : 0.55
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
