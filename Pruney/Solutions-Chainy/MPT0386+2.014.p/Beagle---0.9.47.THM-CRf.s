%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  91 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_38,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,(
    ! [C_46,D_47,A_48] :
      ( r2_hidden(C_46,D_47)
      | ~ r2_hidden(D_47,A_48)
      | ~ r2_hidden(C_46,k1_setfam_1(A_48))
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    ! [C_46] :
      ( r2_hidden(C_46,'#skF_6')
      | ~ r2_hidden(C_46,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_136,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_101,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_6',B_45)
      | ~ r1_tarski('#skF_7',B_45) ) ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_108,c_71])).

tff(c_137,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_120])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_137])).

tff(c_150,plain,(
    ! [C_50] :
      ( r2_hidden(C_50,'#skF_6')
      | ~ r2_hidden(C_50,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_181,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_7'),B_55),'#skF_6')
      | r1_tarski(k1_setfam_1('#skF_7'),B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    r1_tarski(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  %$ r2_hidden > r1_tarski > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 1.92/1.20  
% 1.92/1.20  %Foreground sorts:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Background operators:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Foreground operators:
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.92/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.92/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.92/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.92/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.20  
% 1.92/1.20  tff(f_65, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.92/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.92/1.20  tff(f_60, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 1.92/1.20  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.20  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.20  tff(c_38, plain, (~r1_tarski(k1_setfam_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.92/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.20  tff(c_94, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.20  tff(c_99, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_94])).
% 1.92/1.20  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.92/1.20  tff(c_122, plain, (![C_46, D_47, A_48]: (r2_hidden(C_46, D_47) | ~r2_hidden(D_47, A_48) | ~r2_hidden(C_46, k1_setfam_1(A_48)) | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.20  tff(c_131, plain, (![C_46]: (r2_hidden(C_46, '#skF_6') | ~r2_hidden(C_46, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_40, c_122])).
% 1.92/1.20  tff(c_136, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_131])).
% 1.92/1.20  tff(c_101, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.20  tff(c_108, plain, (![B_45]: (r2_hidden('#skF_6', B_45) | ~r1_tarski('#skF_7', B_45))), inference(resolution, [status(thm)], [c_40, c_101])).
% 1.92/1.20  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.92/1.20  tff(c_68, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.20  tff(c_71, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 1.92/1.20  tff(c_120, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_108, c_71])).
% 1.92/1.20  tff(c_137, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_120])).
% 1.92/1.20  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_137])).
% 1.92/1.20  tff(c_150, plain, (![C_50]: (r2_hidden(C_50, '#skF_6') | ~r2_hidden(C_50, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_131])).
% 1.92/1.20  tff(c_181, plain, (![B_55]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_7'), B_55), '#skF_6') | r1_tarski(k1_setfam_1('#skF_7'), B_55))), inference(resolution, [status(thm)], [c_6, c_150])).
% 1.92/1.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.20  tff(c_189, plain, (r1_tarski(k1_setfam_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_181, c_4])).
% 1.92/1.20  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_189])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 32
% 1.92/1.20  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 2
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 4
% 1.92/1.21  #Demod        : 16
% 1.92/1.21  #Tautology    : 12
% 1.92/1.21  #SimpNegUnit  : 2
% 1.92/1.21  #BackRed      : 8
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.28
% 1.92/1.21  Parsing              : 0.15
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.17
% 1.92/1.21  Inferencing          : 0.06
% 1.92/1.21  Reduction            : 0.05
% 1.92/1.21  Demodulation         : 0.03
% 1.92/1.21  BG Simplification    : 0.02
% 1.92/1.21  Subsumption          : 0.04
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.49
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
