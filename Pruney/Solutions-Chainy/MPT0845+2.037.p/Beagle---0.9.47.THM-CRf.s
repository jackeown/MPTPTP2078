%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   39 (  54 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  90 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_342,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden('#skF_1'(A_96,B_97,C_98),A_96)
      | r2_hidden('#skF_2'(A_96,B_97,C_98),C_98)
      | k4_xboole_0(A_96,B_97) = C_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [A_27,B_28] : ~ r2_hidden(A_27,k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_521,plain,(
    ! [B_105,C_106] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_105,C_106),C_106)
      | k4_xboole_0(k1_xboole_0,B_105) = C_106 ) ),
    inference(resolution,[status(thm)],[c_342,c_66])).

tff(c_549,plain,(
    ! [B_105] : k4_xboole_0(k1_xboole_0,B_105) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_521,c_66])).

tff(c_399,plain,(
    ! [B_97,C_98] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_97,C_98),C_98)
      | k4_xboole_0(k1_xboole_0,B_97) = C_98 ) ),
    inference(resolution,[status(thm)],[c_342,c_66])).

tff(c_550,plain,(
    ! [B_97,C_98] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_97,C_98),C_98)
      | k1_xboole_0 = C_98 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_399])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_160,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,'#skF_4'(A_54,B_55))
      | ~ r2_hidden(D_53,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1686,plain,(
    ! [A_204,B_205,B_206] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_204,B_205),B_206),B_205)
      | ~ r2_hidden(A_204,B_205)
      | r1_xboole_0('#skF_4'(A_204,B_205),B_206) ) ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_1702,plain,(
    ! [A_207,B_208] :
      ( ~ r2_hidden(A_207,B_208)
      | r1_xboole_0('#skF_4'(A_207,B_208),B_208) ) ),
    inference(resolution,[status(thm)],[c_22,c_1686])).

tff(c_72,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_4'(A_31,B_32),B_32)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [B_24] :
      ( ~ r1_xboole_0(B_24,'#skF_5')
      | ~ r2_hidden(B_24,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [A_31] :
      ( ~ r1_xboole_0('#skF_4'(A_31,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_31,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_38])).

tff(c_1711,plain,(
    ! [A_209] : ~ r2_hidden(A_209,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1702,c_81])).

tff(c_1749,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_550,c_1711])).

tff(c_1789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1749])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/2.21  
% 4.34/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/2.21  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.34/2.21  
% 4.34/2.21  %Foreground sorts:
% 4.34/2.21  
% 4.34/2.21  
% 4.34/2.21  %Background operators:
% 4.34/2.21  
% 4.34/2.21  
% 4.34/2.21  %Foreground operators:
% 4.34/2.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.34/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.34/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/2.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.34/2.21  tff('#skF_5', type, '#skF_5': $i).
% 4.34/2.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.34/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.34/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.34/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/2.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.34/2.21  
% 4.68/2.23  tff(f_86, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 4.68/2.23  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.68/2.23  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.68/2.23  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.68/2.23  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.68/2.23  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.68/2.23  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.68/2.23  tff(c_342, plain, (![A_96, B_97, C_98]: (r2_hidden('#skF_1'(A_96, B_97, C_98), A_96) | r2_hidden('#skF_2'(A_96, B_97, C_98), C_98) | k4_xboole_0(A_96, B_97)=C_98)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/2.23  tff(c_28, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/2.23  tff(c_63, plain, (![A_27, B_28]: (~r2_hidden(A_27, k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.68/2.23  tff(c_66, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_63])).
% 4.68/2.23  tff(c_521, plain, (![B_105, C_106]: (r2_hidden('#skF_2'(k1_xboole_0, B_105, C_106), C_106) | k4_xboole_0(k1_xboole_0, B_105)=C_106)), inference(resolution, [status(thm)], [c_342, c_66])).
% 4.68/2.23  tff(c_549, plain, (![B_105]: (k4_xboole_0(k1_xboole_0, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_521, c_66])).
% 4.68/2.23  tff(c_399, plain, (![B_97, C_98]: (r2_hidden('#skF_2'(k1_xboole_0, B_97, C_98), C_98) | k4_xboole_0(k1_xboole_0, B_97)=C_98)), inference(resolution, [status(thm)], [c_342, c_66])).
% 4.68/2.23  tff(c_550, plain, (![B_97, C_98]: (r2_hidden('#skF_2'(k1_xboole_0, B_97, C_98), C_98) | k1_xboole_0=C_98)), inference(demodulation, [status(thm), theory('equality')], [c_549, c_399])).
% 4.68/2.23  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.68/2.23  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.68/2.23  tff(c_160, plain, (![D_53, A_54, B_55]: (~r2_hidden(D_53, '#skF_4'(A_54, B_55)) | ~r2_hidden(D_53, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/2.23  tff(c_1686, plain, (![A_204, B_205, B_206]: (~r2_hidden('#skF_3'('#skF_4'(A_204, B_205), B_206), B_205) | ~r2_hidden(A_204, B_205) | r1_xboole_0('#skF_4'(A_204, B_205), B_206))), inference(resolution, [status(thm)], [c_24, c_160])).
% 4.68/2.23  tff(c_1702, plain, (![A_207, B_208]: (~r2_hidden(A_207, B_208) | r1_xboole_0('#skF_4'(A_207, B_208), B_208))), inference(resolution, [status(thm)], [c_22, c_1686])).
% 4.68/2.23  tff(c_72, plain, (![A_31, B_32]: (r2_hidden('#skF_4'(A_31, B_32), B_32) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/2.23  tff(c_38, plain, (![B_24]: (~r1_xboole_0(B_24, '#skF_5') | ~r2_hidden(B_24, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.68/2.23  tff(c_81, plain, (![A_31]: (~r1_xboole_0('#skF_4'(A_31, '#skF_5'), '#skF_5') | ~r2_hidden(A_31, '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_38])).
% 4.68/2.23  tff(c_1711, plain, (![A_209]: (~r2_hidden(A_209, '#skF_5'))), inference(resolution, [status(thm)], [c_1702, c_81])).
% 4.68/2.23  tff(c_1749, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_550, c_1711])).
% 4.68/2.23  tff(c_1789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1749])).
% 4.68/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/2.23  
% 4.68/2.23  Inference rules
% 4.68/2.23  ----------------------
% 4.68/2.23  #Ref     : 0
% 4.68/2.23  #Sup     : 368
% 4.68/2.23  #Fact    : 0
% 4.68/2.23  #Define  : 0
% 4.68/2.23  #Split   : 2
% 4.68/2.23  #Chain   : 0
% 4.68/2.23  #Close   : 0
% 4.68/2.23  
% 4.68/2.23  Ordering : KBO
% 4.68/2.23  
% 4.68/2.23  Simplification rules
% 4.68/2.23  ----------------------
% 4.68/2.23  #Subsume      : 87
% 4.68/2.23  #Demod        : 148
% 4.68/2.23  #Tautology    : 102
% 4.68/2.23  #SimpNegUnit  : 21
% 4.68/2.23  #BackRed      : 10
% 4.68/2.23  
% 4.68/2.23  #Partial instantiations: 0
% 4.68/2.23  #Strategies tried      : 1
% 4.68/2.23  
% 4.68/2.23  Timing (in seconds)
% 4.68/2.23  ----------------------
% 4.68/2.23  Preprocessing        : 0.46
% 4.68/2.23  Parsing              : 0.23
% 4.68/2.23  CNF conversion       : 0.04
% 4.68/2.23  Main loop            : 0.86
% 4.68/2.23  Inferencing          : 0.32
% 4.68/2.23  Reduction            : 0.23
% 4.68/2.23  Demodulation         : 0.16
% 4.68/2.23  BG Simplification    : 0.05
% 4.68/2.23  Subsumption          : 0.20
% 4.68/2.23  Abstraction          : 0.04
% 4.68/2.23  MUC search           : 0.00
% 4.68/2.24  Cooper               : 0.00
% 4.68/2.24  Total                : 1.37
% 4.68/2.24  Index Insertion      : 0.00
% 4.68/2.24  Index Deletion       : 0.00
% 4.68/2.24  Index Matching       : 0.00
% 4.68/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
