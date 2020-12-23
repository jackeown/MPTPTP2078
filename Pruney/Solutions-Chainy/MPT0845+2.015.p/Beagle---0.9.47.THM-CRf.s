%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   45 (  79 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 152 expanded)
%              Number of equality atoms :   19 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_251,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_3'(A_109,B_110,C_111),A_109)
      | r2_hidden('#skF_5'(A_109,B_110,C_111),C_111)
      | k2_zfmisc_1(A_109,B_110) = C_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_40] : k2_zfmisc_1(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    ! [A_55,B_56] : ~ r2_hidden(A_55,k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_69])).

tff(c_281,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_3'(A_109,B_110,k1_xboole_0),A_109)
      | k2_zfmisc_1(A_109,B_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_251,c_72])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [D_75,A_76,B_77] :
      ( ~ r2_hidden(D_75,'#skF_8'(A_76,B_77))
      | ~ r2_hidden(D_75,B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_304,plain,(
    ! [A_118,B_119,B_120] :
      ( ~ r2_hidden('#skF_1'('#skF_8'(A_118,B_119),B_120),B_119)
      | ~ r2_hidden(A_118,B_119)
      | r1_xboole_0('#skF_8'(A_118,B_119),B_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_310,plain,(
    ! [A_121,B_122] :
      ( ~ r2_hidden(A_121,B_122)
      | r1_xboole_0('#skF_8'(A_121,B_122),B_122) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_91,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_8'(A_63,B_64),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [B_52] :
      ( ~ r1_xboole_0(B_52,'#skF_9')
      | ~ r2_hidden(B_52,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_100,plain,(
    ! [A_63] :
      ( ~ r1_xboole_0('#skF_8'(A_63,'#skF_9'),'#skF_9')
      | ~ r2_hidden(A_63,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_91,c_44])).

tff(c_351,plain,(
    ! [A_126] : ~ r2_hidden(A_126,'#skF_9') ),
    inference(resolution,[status(thm)],[c_310,c_100])).

tff(c_436,plain,(
    ! [B_131] : k2_zfmisc_1('#skF_9',B_131) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_281,c_351])).

tff(c_32,plain,(
    ! [B_41,A_40] :
      ( k1_xboole_0 = B_41
      | k1_xboole_0 = A_40
      | k2_zfmisc_1(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_450,plain,(
    ! [B_131] :
      ( k1_xboole_0 = B_131
      | k1_xboole_0 = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_32])).

tff(c_474,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_450])).

tff(c_469,plain,(
    ! [B_131] : k1_xboole_0 = B_131 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_450])).

tff(c_546,plain,(
    ! [B_958] : B_958 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_469])).

tff(c_615,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1
% 2.60/1.40  
% 2.60/1.40  %Foreground sorts:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Background operators:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Foreground operators:
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.60/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.60/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.60/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.40  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.60/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.60/1.40  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.60/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.40  
% 2.60/1.41  tff(f_88, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.60/1.41  tff(f_55, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.60/1.41  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.60/1.41  tff(f_64, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.60/1.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.60/1.41  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.60/1.41  tff(c_46, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.41  tff(c_251, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_3'(A_109, B_110, C_111), A_109) | r2_hidden('#skF_5'(A_109, B_110, C_111), C_111) | k2_zfmisc_1(A_109, B_110)=C_111)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.60/1.41  tff(c_34, plain, (![A_40]: (k2_zfmisc_1(A_40, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.41  tff(c_69, plain, (![A_55, B_56]: (~r2_hidden(A_55, k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.41  tff(c_72, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_69])).
% 2.60/1.41  tff(c_281, plain, (![A_109, B_110]: (r2_hidden('#skF_3'(A_109, B_110, k1_xboole_0), A_109) | k2_zfmisc_1(A_109, B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_251, c_72])).
% 2.60/1.41  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.41  tff(c_134, plain, (![D_75, A_76, B_77]: (~r2_hidden(D_75, '#skF_8'(A_76, B_77)) | ~r2_hidden(D_75, B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.41  tff(c_304, plain, (![A_118, B_119, B_120]: (~r2_hidden('#skF_1'('#skF_8'(A_118, B_119), B_120), B_119) | ~r2_hidden(A_118, B_119) | r1_xboole_0('#skF_8'(A_118, B_119), B_120))), inference(resolution, [status(thm)], [c_6, c_134])).
% 2.60/1.41  tff(c_310, plain, (![A_121, B_122]: (~r2_hidden(A_121, B_122) | r1_xboole_0('#skF_8'(A_121, B_122), B_122))), inference(resolution, [status(thm)], [c_4, c_304])).
% 2.60/1.41  tff(c_91, plain, (![A_63, B_64]: (r2_hidden('#skF_8'(A_63, B_64), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.41  tff(c_44, plain, (![B_52]: (~r1_xboole_0(B_52, '#skF_9') | ~r2_hidden(B_52, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.41  tff(c_100, plain, (![A_63]: (~r1_xboole_0('#skF_8'(A_63, '#skF_9'), '#skF_9') | ~r2_hidden(A_63, '#skF_9'))), inference(resolution, [status(thm)], [c_91, c_44])).
% 2.60/1.41  tff(c_351, plain, (![A_126]: (~r2_hidden(A_126, '#skF_9'))), inference(resolution, [status(thm)], [c_310, c_100])).
% 2.60/1.41  tff(c_436, plain, (![B_131]: (k2_zfmisc_1('#skF_9', B_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_281, c_351])).
% 2.60/1.41  tff(c_32, plain, (![B_41, A_40]: (k1_xboole_0=B_41 | k1_xboole_0=A_40 | k2_zfmisc_1(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.41  tff(c_450, plain, (![B_131]: (k1_xboole_0=B_131 | k1_xboole_0='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_436, c_32])).
% 2.60/1.41  tff(c_474, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_46, c_450])).
% 2.60/1.41  tff(c_469, plain, (![B_131]: (k1_xboole_0=B_131)), inference(negUnitSimplification, [status(thm)], [c_46, c_450])).
% 2.60/1.41  tff(c_546, plain, (![B_958]: (B_958='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_474, c_469])).
% 2.60/1.41  tff(c_615, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_546, c_46])).
% 2.60/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.41  
% 2.60/1.41  Inference rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Ref     : 0
% 2.60/1.41  #Sup     : 149
% 2.60/1.41  #Fact    : 0
% 2.60/1.41  #Define  : 0
% 2.60/1.41  #Split   : 0
% 2.60/1.41  #Chain   : 0
% 2.60/1.41  #Close   : 0
% 2.60/1.41  
% 2.60/1.41  Ordering : KBO
% 2.60/1.41  
% 2.60/1.41  Simplification rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Subsume      : 44
% 2.60/1.41  #Demod        : 26
% 2.60/1.41  #Tautology    : 21
% 2.60/1.41  #SimpNegUnit  : 9
% 2.60/1.41  #BackRed      : 4
% 2.60/1.41  
% 2.60/1.41  #Partial instantiations: 29
% 2.60/1.41  #Strategies tried      : 1
% 2.60/1.41  
% 2.60/1.41  Timing (in seconds)
% 2.60/1.41  ----------------------
% 2.60/1.41  Preprocessing        : 0.32
% 2.60/1.41  Parsing              : 0.16
% 2.60/1.41  CNF conversion       : 0.03
% 2.60/1.41  Main loop            : 0.31
% 2.60/1.41  Inferencing          : 0.14
% 2.60/1.41  Reduction            : 0.08
% 2.60/1.41  Demodulation         : 0.05
% 2.60/1.41  BG Simplification    : 0.02
% 2.60/1.41  Subsumption          : 0.05
% 2.60/1.41  Abstraction          : 0.01
% 2.60/1.41  MUC search           : 0.00
% 2.60/1.41  Cooper               : 0.00
% 2.60/1.41  Total                : 0.66
% 2.60/1.41  Index Insertion      : 0.00
% 2.60/1.41  Index Deletion       : 0.00
% 2.60/1.41  Index Matching       : 0.00
% 2.60/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
