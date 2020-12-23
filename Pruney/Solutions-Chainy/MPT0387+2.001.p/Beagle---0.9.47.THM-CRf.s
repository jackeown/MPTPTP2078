%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 121 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 214 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_68,plain,(
    k1_setfam_1('#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [A_59] : r1_tarski(A_59,A_59) ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_152,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_32])).

tff(c_228,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(A_70,B_71)
      | k4_xboole_0(k1_tarski(A_70),B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_238,plain,(
    ! [A_72] : r2_hidden(A_72,k1_tarski(A_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_228])).

tff(c_171,plain,(
    ! [D_61,B_62,A_63] :
      ( ~ r2_hidden(D_61,B_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [D_61,A_59] :
      ( ~ r2_hidden(D_61,A_59)
      | ~ r2_hidden(D_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_171])).

tff(c_243,plain,(
    ! [A_72] : ~ r2_hidden(A_72,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_238,c_174])).

tff(c_70,plain,(
    r2_hidden(k1_xboole_0,'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_641,plain,(
    ! [C_112,D_113,A_114] :
      ( r2_hidden(C_112,D_113)
      | ~ r2_hidden(D_113,A_114)
      | ~ r2_hidden(C_112,k1_setfam_1(A_114))
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_657,plain,(
    ! [C_112] :
      ( r2_hidden(C_112,k1_xboole_0)
      | ~ r2_hidden(C_112,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_70,c_641])).

tff(c_669,plain,(
    ! [C_112] :
      ( ~ r2_hidden(C_112,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_657])).

tff(c_671,plain,(
    ! [C_115] : ~ r2_hidden(C_115,k1_setfam_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_691,plain,(
    k1_setfam_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_671])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_691])).

tff(c_700,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_306,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_319,plain,(
    ! [B_84] :
      ( r2_hidden(k1_xboole_0,B_84)
      | ~ r1_tarski('#skF_9',B_84) ) ),
    inference(resolution,[status(thm)],[c_70,c_306])).

tff(c_347,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_319,c_243])).

tff(c_715,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_347])).

tff(c_734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:52:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  
% 2.85/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1
% 2.85/1.47  
% 2.85/1.47  %Foreground sorts:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Background operators:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Foreground operators:
% 2.85/1.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.85/1.47  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.85/1.47  tff('#skF_9', type, '#skF_9': $i).
% 2.85/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.47  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.85/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.85/1.47  
% 2.85/1.48  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.85/1.48  tff(f_94, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 2.85/1.48  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.85/1.48  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.85/1.48  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 2.85/1.48  tff(f_47, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.85/1.48  tff(f_89, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.85/1.48  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.48  tff(c_141, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.48  tff(c_146, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_141])).
% 2.85/1.48  tff(c_68, plain, (k1_setfam_1('#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.85/1.48  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.85/1.48  tff(c_148, plain, (![A_59]: (r1_tarski(A_59, A_59))), inference(resolution, [status(thm)], [c_8, c_141])).
% 2.85/1.48  tff(c_32, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.48  tff(c_152, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_148, c_32])).
% 2.85/1.48  tff(c_228, plain, (![A_70, B_71]: (r2_hidden(A_70, B_71) | k4_xboole_0(k1_tarski(A_70), B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.85/1.48  tff(c_238, plain, (![A_72]: (r2_hidden(A_72, k1_tarski(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_228])).
% 2.85/1.48  tff(c_171, plain, (![D_61, B_62, A_63]: (~r2_hidden(D_61, B_62) | ~r2_hidden(D_61, k4_xboole_0(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.85/1.48  tff(c_174, plain, (![D_61, A_59]: (~r2_hidden(D_61, A_59) | ~r2_hidden(D_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_171])).
% 2.85/1.48  tff(c_243, plain, (![A_72]: (~r2_hidden(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_238, c_174])).
% 2.85/1.48  tff(c_70, plain, (r2_hidden(k1_xboole_0, '#skF_9')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.85/1.48  tff(c_641, plain, (![C_112, D_113, A_114]: (r2_hidden(C_112, D_113) | ~r2_hidden(D_113, A_114) | ~r2_hidden(C_112, k1_setfam_1(A_114)) | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.48  tff(c_657, plain, (![C_112]: (r2_hidden(C_112, k1_xboole_0) | ~r2_hidden(C_112, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_70, c_641])).
% 2.85/1.48  tff(c_669, plain, (![C_112]: (~r2_hidden(C_112, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_243, c_657])).
% 2.85/1.48  tff(c_671, plain, (![C_115]: (~r2_hidden(C_115, k1_setfam_1('#skF_9')))), inference(splitLeft, [status(thm)], [c_669])).
% 2.85/1.48  tff(c_691, plain, (k1_setfam_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_671])).
% 2.85/1.48  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_691])).
% 2.85/1.48  tff(c_700, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_669])).
% 2.85/1.48  tff(c_306, plain, (![C_81, B_82, A_83]: (r2_hidden(C_81, B_82) | ~r2_hidden(C_81, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.48  tff(c_319, plain, (![B_84]: (r2_hidden(k1_xboole_0, B_84) | ~r1_tarski('#skF_9', B_84))), inference(resolution, [status(thm)], [c_70, c_306])).
% 2.85/1.48  tff(c_347, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_319, c_243])).
% 2.85/1.48  tff(c_715, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_700, c_347])).
% 2.85/1.48  tff(c_734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_715])).
% 2.85/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.48  
% 2.85/1.48  Inference rules
% 2.85/1.48  ----------------------
% 2.85/1.48  #Ref     : 0
% 2.85/1.48  #Sup     : 142
% 2.85/1.48  #Fact    : 0
% 2.85/1.48  #Define  : 0
% 2.85/1.48  #Split   : 1
% 2.85/1.48  #Chain   : 0
% 2.85/1.48  #Close   : 0
% 2.85/1.48  
% 2.85/1.48  Ordering : KBO
% 2.85/1.48  
% 2.85/1.48  Simplification rules
% 2.85/1.48  ----------------------
% 2.85/1.48  #Subsume      : 32
% 2.85/1.48  #Demod        : 55
% 2.85/1.48  #Tautology    : 50
% 2.85/1.48  #SimpNegUnit  : 10
% 2.85/1.48  #BackRed      : 31
% 2.85/1.48  
% 2.85/1.48  #Partial instantiations: 0
% 2.85/1.48  #Strategies tried      : 1
% 2.85/1.48  
% 2.85/1.48  Timing (in seconds)
% 2.85/1.48  ----------------------
% 2.85/1.49  Preprocessing        : 0.32
% 2.85/1.49  Parsing              : 0.16
% 2.85/1.49  CNF conversion       : 0.03
% 2.85/1.49  Main loop            : 0.38
% 2.85/1.49  Inferencing          : 0.12
% 2.85/1.49  Reduction            : 0.12
% 2.85/1.49  Demodulation         : 0.08
% 2.85/1.49  BG Simplification    : 0.02
% 2.85/1.49  Subsumption          : 0.10
% 2.85/1.49  Abstraction          : 0.02
% 2.85/1.49  MUC search           : 0.00
% 2.85/1.49  Cooper               : 0.00
% 2.85/1.49  Total                : 0.74
% 2.85/1.49  Index Insertion      : 0.00
% 2.85/1.49  Index Deletion       : 0.00
% 2.85/1.49  Index Matching       : 0.00
% 2.85/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
