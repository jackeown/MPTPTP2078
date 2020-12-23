%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:38 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  77 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_38,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k1_tarski(A_40),B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(k1_tarski(A_55),B_56) = B_56
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(k1_tarski(A_60),C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r2_hidden(A_60,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_83,plain,(
    ! [A_63] :
      ( r1_tarski(k1_tarski(A_63),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(A_63,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_30,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | ~ r1_tarski(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [A_63] :
      ( r2_hidden(A_63,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(A_63,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_83,c_30])).

tff(c_12,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_5'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),A_6)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),B_7)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [A_95,B_96,D_97] :
      ( k4_tarski('#skF_5'(A_95,B_96,k2_zfmisc_1(A_95,B_96),D_97),'#skF_6'(A_95,B_96,k2_zfmisc_1(A_95,B_96),D_97)) = D_97
      | ~ r2_hidden(D_97,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [E_44,F_45] :
      ( k4_tarski(E_44,F_45) != '#skF_10'
      | ~ r2_hidden(F_45,'#skF_9')
      | ~ r2_hidden(E_44,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_244,plain,(
    ! [D_115,A_116,B_117] :
      ( D_115 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_116,B_117,k2_zfmisc_1(A_116,B_117),D_115),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_116,B_117,k2_zfmisc_1(A_116,B_117),D_115),'#skF_8')
      | ~ r2_hidden(D_115,k2_zfmisc_1(A_116,B_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_34])).

tff(c_256,plain,(
    ! [D_118,A_119] :
      ( D_118 != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_119,'#skF_9',k2_zfmisc_1(A_119,'#skF_9'),D_118),'#skF_8')
      | ~ r2_hidden(D_118,k2_zfmisc_1(A_119,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10,c_244])).

tff(c_263,plain,(
    ! [D_120] :
      ( D_120 != '#skF_10'
      | ~ r2_hidden(D_120,k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_12,c_256])).

tff(c_308,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_93,c_263])).

tff(c_36,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:13:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.11/1.30  
% 2.11/1.30  %Foreground sorts:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Background operators:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Foreground operators:
% 2.11/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.11/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.11/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.11/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.11/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.11/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.11/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.30  
% 2.11/1.31  tff(f_63, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.11/1.31  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.11/1.31  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.31  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.11/1.31  tff(f_45, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.11/1.31  tff(c_38, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.31  tff(c_32, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), B_41) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.31  tff(c_40, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.31  tff(c_62, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)=B_56 | ~r2_hidden(A_55, B_56))), inference(resolution, [status(thm)], [c_32, c_40])).
% 2.11/1.31  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.31  tff(c_76, plain, (![A_60, C_61, B_62]: (r1_tarski(k1_tarski(A_60), C_61) | ~r1_tarski(B_62, C_61) | ~r2_hidden(A_60, B_62))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2])).
% 2.11/1.31  tff(c_83, plain, (![A_63]: (r1_tarski(k1_tarski(A_63), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(A_63, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_76])).
% 2.11/1.31  tff(c_30, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | ~r1_tarski(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.31  tff(c_93, plain, (![A_63]: (r2_hidden(A_63, k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(A_63, '#skF_7'))), inference(resolution, [status(thm)], [c_83, c_30])).
% 2.11/1.31  tff(c_12, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_5'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), A_6) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.31  tff(c_10, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), B_7) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.31  tff(c_191, plain, (![A_95, B_96, D_97]: (k4_tarski('#skF_5'(A_95, B_96, k2_zfmisc_1(A_95, B_96), D_97), '#skF_6'(A_95, B_96, k2_zfmisc_1(A_95, B_96), D_97))=D_97 | ~r2_hidden(D_97, k2_zfmisc_1(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.31  tff(c_34, plain, (![E_44, F_45]: (k4_tarski(E_44, F_45)!='#skF_10' | ~r2_hidden(F_45, '#skF_9') | ~r2_hidden(E_44, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.31  tff(c_244, plain, (![D_115, A_116, B_117]: (D_115!='#skF_10' | ~r2_hidden('#skF_6'(A_116, B_117, k2_zfmisc_1(A_116, B_117), D_115), '#skF_9') | ~r2_hidden('#skF_5'(A_116, B_117, k2_zfmisc_1(A_116, B_117), D_115), '#skF_8') | ~r2_hidden(D_115, k2_zfmisc_1(A_116, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_34])).
% 2.11/1.31  tff(c_256, plain, (![D_118, A_119]: (D_118!='#skF_10' | ~r2_hidden('#skF_5'(A_119, '#skF_9', k2_zfmisc_1(A_119, '#skF_9'), D_118), '#skF_8') | ~r2_hidden(D_118, k2_zfmisc_1(A_119, '#skF_9')))), inference(resolution, [status(thm)], [c_10, c_244])).
% 2.11/1.31  tff(c_263, plain, (![D_120]: (D_120!='#skF_10' | ~r2_hidden(D_120, k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_12, c_256])).
% 2.11/1.31  tff(c_308, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_93, c_263])).
% 2.11/1.31  tff(c_36, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.31  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_36])).
% 2.11/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  Inference rules
% 2.11/1.31  ----------------------
% 2.11/1.31  #Ref     : 0
% 2.11/1.31  #Sup     : 60
% 2.11/1.31  #Fact    : 0
% 2.11/1.31  #Define  : 0
% 2.11/1.31  #Split   : 0
% 2.11/1.31  #Chain   : 0
% 2.11/1.31  #Close   : 0
% 2.11/1.31  
% 2.11/1.31  Ordering : KBO
% 2.11/1.31  
% 2.11/1.31  Simplification rules
% 2.11/1.31  ----------------------
% 2.11/1.31  #Subsume      : 1
% 2.11/1.31  #Demod        : 0
% 2.11/1.31  #Tautology    : 11
% 2.11/1.31  #SimpNegUnit  : 1
% 2.11/1.31  #BackRed      : 1
% 2.11/1.31  
% 2.11/1.31  #Partial instantiations: 0
% 2.11/1.31  #Strategies tried      : 1
% 2.11/1.31  
% 2.11/1.31  Timing (in seconds)
% 2.11/1.31  ----------------------
% 2.11/1.32  Preprocessing        : 0.28
% 2.11/1.32  Parsing              : 0.14
% 2.11/1.32  CNF conversion       : 0.03
% 2.11/1.32  Main loop            : 0.24
% 2.11/1.32  Inferencing          : 0.10
% 2.11/1.32  Reduction            : 0.05
% 2.11/1.32  Demodulation         : 0.03
% 2.11/1.32  BG Simplification    : 0.02
% 2.11/1.32  Subsumption          : 0.06
% 2.11/1.32  Abstraction          : 0.01
% 2.11/1.32  MUC search           : 0.00
% 2.11/1.32  Cooper               : 0.00
% 2.11/1.32  Total                : 0.55
% 2.11/1.32  Index Insertion      : 0.00
% 2.11/1.32  Index Deletion       : 0.00
% 2.11/1.32  Index Matching       : 0.00
% 2.11/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
