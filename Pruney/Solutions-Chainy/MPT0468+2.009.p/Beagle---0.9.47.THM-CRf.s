%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  58 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_6 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_92,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(k4_tarski('#skF_4'(A_50,B_51),'#skF_5'(A_50,B_51)),A_50)
      | r1_tarski(A_50,B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [B_35,C_36] : ~ r2_hidden(k4_tarski(B_35,C_36),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_96,plain,(
    ! [B_51] :
      ( r1_tarski('#skF_6',B_51)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_92,c_30])).

tff(c_106,plain,(
    ! [B_51] : r1_tarski('#skF_6',B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_hidden('#skF_2'(A_56,B_57,C_58,D_59),B_57)
      | ~ r2_hidden(D_59,A_56)
      | ~ r1_tarski(A_56,k2_zfmisc_1(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_122,plain,(
    ! [D_59,A_56,C_58] :
      ( ~ r2_hidden(D_59,A_56)
      | ~ r1_tarski(A_56,k2_zfmisc_1(k1_xboole_0,C_58)) ) ),
    inference(resolution,[status(thm)],[c_118,c_60])).

tff(c_129,plain,(
    ! [D_60,A_61] :
      ( ~ r2_hidden(D_60,A_61)
      | ~ r1_tarski(A_61,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_122])).

tff(c_142,plain,(
    ! [A_62] :
      ( ~ r1_tarski(A_62,k1_xboole_0)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_153,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_106,c_142])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_153,c_6])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_6 > #skF_3 > #skF_5 > #skF_4
% 1.95/1.24  
% 1.95/1.24  %Foreground sorts:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Background operators:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Foreground operators:
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.95/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.95/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.95/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.24  
% 1.95/1.25  tff(f_76, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.95/1.25  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.95/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.95/1.25  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.95/1.25  tff(f_48, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 1.95/1.25  tff(f_57, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.95/1.25  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.95/1.25  tff(c_28, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.95/1.25  tff(c_32, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.95/1.25  tff(c_92, plain, (![A_50, B_51]: (r2_hidden(k4_tarski('#skF_4'(A_50, B_51), '#skF_5'(A_50, B_51)), A_50) | r1_tarski(A_50, B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.25  tff(c_30, plain, (![B_35, C_36]: (~r2_hidden(k4_tarski(B_35, C_36), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.95/1.25  tff(c_96, plain, (![B_51]: (r1_tarski('#skF_6', B_51) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_92, c_30])).
% 1.95/1.25  tff(c_106, plain, (![B_51]: (r1_tarski('#skF_6', B_51))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96])).
% 1.95/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.25  tff(c_18, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.25  tff(c_118, plain, (![A_56, B_57, C_58, D_59]: (r2_hidden('#skF_2'(A_56, B_57, C_58, D_59), B_57) | ~r2_hidden(D_59, A_56) | ~r1_tarski(A_56, k2_zfmisc_1(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.25  tff(c_16, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.25  tff(c_57, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.25  tff(c_60, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_57])).
% 1.95/1.25  tff(c_122, plain, (![D_59, A_56, C_58]: (~r2_hidden(D_59, A_56) | ~r1_tarski(A_56, k2_zfmisc_1(k1_xboole_0, C_58)))), inference(resolution, [status(thm)], [c_118, c_60])).
% 1.95/1.25  tff(c_129, plain, (![D_60, A_61]: (~r2_hidden(D_60, A_61) | ~r1_tarski(A_61, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_122])).
% 1.95/1.25  tff(c_142, plain, (![A_62]: (~r1_tarski(A_62, k1_xboole_0) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_4, c_129])).
% 1.95/1.25  tff(c_153, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_106, c_142])).
% 1.95/1.25  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.25  tff(c_156, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_153, c_6])).
% 1.95/1.25  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_156])).
% 1.95/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  Inference rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Ref     : 0
% 1.95/1.25  #Sup     : 25
% 1.95/1.25  #Fact    : 0
% 1.95/1.25  #Define  : 0
% 1.95/1.25  #Split   : 1
% 1.95/1.25  #Chain   : 0
% 1.95/1.25  #Close   : 0
% 1.95/1.25  
% 1.95/1.25  Ordering : KBO
% 1.95/1.25  
% 1.95/1.25  Simplification rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Subsume      : 2
% 1.95/1.25  #Demod        : 3
% 1.95/1.25  #Tautology    : 10
% 1.95/1.25  #SimpNegUnit  : 1
% 1.95/1.25  #BackRed      : 0
% 1.95/1.25  
% 1.95/1.25  #Partial instantiations: 0
% 1.95/1.25  #Strategies tried      : 1
% 1.95/1.25  
% 1.95/1.25  Timing (in seconds)
% 1.95/1.25  ----------------------
% 1.95/1.25  Preprocessing        : 0.31
% 1.95/1.25  Parsing              : 0.17
% 1.95/1.25  CNF conversion       : 0.02
% 1.95/1.25  Main loop            : 0.12
% 1.95/1.25  Inferencing          : 0.04
% 1.95/1.25  Reduction            : 0.03
% 1.95/1.25  Demodulation         : 0.02
% 1.95/1.25  BG Simplification    : 0.01
% 1.95/1.25  Subsumption          : 0.02
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.25  MUC search           : 0.00
% 1.95/1.25  Cooper               : 0.00
% 1.95/1.25  Total                : 0.46
% 1.95/1.25  Index Insertion      : 0.00
% 1.95/1.25  Index Deletion       : 0.00
% 1.95/1.25  Index Matching       : 0.00
% 1.95/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
