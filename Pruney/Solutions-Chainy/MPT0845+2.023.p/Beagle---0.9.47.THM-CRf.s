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
% DateTime   : Thu Dec  3 10:08:47 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  68 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_63,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_246,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_3'(A_82,B_83),A_82)
      | r2_hidden('#skF_4'(A_82,B_83),B_83)
      | k3_tarski(A_82) = B_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_25] : k2_zfmisc_1(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    ! [A_40,B_41] : ~ r2_hidden(A_40,k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_25] : ~ r2_hidden(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_69])).

tff(c_265,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_83),B_83)
      | k3_tarski(k1_xboole_0) = B_83 ) ),
    inference(resolution,[status(thm)],[c_246,c_75])).

tff(c_295,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_83),B_83)
      | k1_xboole_0 = B_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_265])).

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

tff(c_164,plain,(
    ! [D_65,A_66,B_67] :
      ( ~ r2_hidden(D_65,'#skF_6'(A_66,B_67))
      | ~ r2_hidden(D_65,B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_442,plain,(
    ! [A_102,B_103,B_104] :
      ( ~ r2_hidden('#skF_1'('#skF_6'(A_102,B_103),B_104),B_103)
      | ~ r2_hidden(A_102,B_103)
      | r1_xboole_0('#skF_6'(A_102,B_103),B_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_458,plain,(
    ! [A_105,B_106] :
      ( ~ r2_hidden(A_105,B_106)
      | r1_xboole_0('#skF_6'(A_105,B_106),B_106) ) ),
    inference(resolution,[status(thm)],[c_4,c_442])).

tff(c_78,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_6'(A_44,B_45),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [B_37] :
      ( ~ r1_xboole_0(B_37,'#skF_7')
      | ~ r2_hidden(B_37,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    ! [A_44] :
      ( ~ r1_xboole_0('#skF_6'(A_44,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_44,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_40])).

tff(c_467,plain,(
    ! [A_107] : ~ r2_hidden(A_107,'#skF_7') ),
    inference(resolution,[status(thm)],[c_458,c_88])).

tff(c_475,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_295,c_467])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  
% 2.41/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  %$ r2_hidden > r1_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.41/1.36  
% 2.41/1.36  %Foreground sorts:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Background operators:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Foreground operators:
% 2.41/1.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.41/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.41/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.41/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.41/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.41/1.36  
% 2.41/1.37  tff(f_87, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.41/1.37  tff(f_63, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.41/1.37  tff(f_53, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.41/1.37  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.41/1.37  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.41/1.37  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.41/1.37  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.41/1.37  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.41/1.37  tff(c_34, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.41/1.37  tff(c_246, plain, (![A_82, B_83]: (r2_hidden('#skF_3'(A_82, B_83), A_82) | r2_hidden('#skF_4'(A_82, B_83), B_83) | k3_tarski(A_82)=B_83)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.37  tff(c_28, plain, (![A_25]: (k2_zfmisc_1(A_25, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.41/1.37  tff(c_69, plain, (![A_40, B_41]: (~r2_hidden(A_40, k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.37  tff(c_75, plain, (![A_25]: (~r2_hidden(A_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_69])).
% 2.41/1.37  tff(c_265, plain, (![B_83]: (r2_hidden('#skF_4'(k1_xboole_0, B_83), B_83) | k3_tarski(k1_xboole_0)=B_83)), inference(resolution, [status(thm)], [c_246, c_75])).
% 2.41/1.37  tff(c_295, plain, (![B_83]: (r2_hidden('#skF_4'(k1_xboole_0, B_83), B_83) | k1_xboole_0=B_83)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_265])).
% 2.41/1.37  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.37  tff(c_164, plain, (![D_65, A_66, B_67]: (~r2_hidden(D_65, '#skF_6'(A_66, B_67)) | ~r2_hidden(D_65, B_67) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.37  tff(c_442, plain, (![A_102, B_103, B_104]: (~r2_hidden('#skF_1'('#skF_6'(A_102, B_103), B_104), B_103) | ~r2_hidden(A_102, B_103) | r1_xboole_0('#skF_6'(A_102, B_103), B_104))), inference(resolution, [status(thm)], [c_6, c_164])).
% 2.41/1.37  tff(c_458, plain, (![A_105, B_106]: (~r2_hidden(A_105, B_106) | r1_xboole_0('#skF_6'(A_105, B_106), B_106))), inference(resolution, [status(thm)], [c_4, c_442])).
% 2.41/1.37  tff(c_78, plain, (![A_44, B_45]: (r2_hidden('#skF_6'(A_44, B_45), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.37  tff(c_40, plain, (![B_37]: (~r1_xboole_0(B_37, '#skF_7') | ~r2_hidden(B_37, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.41/1.37  tff(c_88, plain, (![A_44]: (~r1_xboole_0('#skF_6'(A_44, '#skF_7'), '#skF_7') | ~r2_hidden(A_44, '#skF_7'))), inference(resolution, [status(thm)], [c_78, c_40])).
% 2.41/1.37  tff(c_467, plain, (![A_107]: (~r2_hidden(A_107, '#skF_7'))), inference(resolution, [status(thm)], [c_458, c_88])).
% 2.41/1.37  tff(c_475, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_295, c_467])).
% 2.41/1.37  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_475])).
% 2.41/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.37  
% 2.41/1.37  Inference rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Ref     : 0
% 2.41/1.37  #Sup     : 98
% 2.41/1.37  #Fact    : 0
% 2.41/1.37  #Define  : 0
% 2.41/1.37  #Split   : 2
% 2.41/1.37  #Chain   : 0
% 2.41/1.37  #Close   : 0
% 2.41/1.37  
% 2.41/1.37  Ordering : KBO
% 2.41/1.37  
% 2.41/1.37  Simplification rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Subsume      : 13
% 2.41/1.37  #Demod        : 4
% 2.41/1.37  #Tautology    : 12
% 2.41/1.37  #SimpNegUnit  : 5
% 2.41/1.37  #BackRed      : 0
% 2.41/1.37  
% 2.41/1.37  #Partial instantiations: 0
% 2.41/1.37  #Strategies tried      : 1
% 2.41/1.37  
% 2.41/1.37  Timing (in seconds)
% 2.41/1.37  ----------------------
% 2.41/1.37  Preprocessing        : 0.28
% 2.41/1.37  Parsing              : 0.14
% 2.41/1.37  CNF conversion       : 0.02
% 2.41/1.37  Main loop            : 0.28
% 2.41/1.37  Inferencing          : 0.11
% 2.41/1.37  Reduction            : 0.07
% 2.41/1.38  Demodulation         : 0.05
% 2.41/1.38  BG Simplification    : 0.02
% 2.41/1.38  Subsumption          : 0.06
% 2.41/1.38  Abstraction          : 0.01
% 2.41/1.38  MUC search           : 0.00
% 2.41/1.38  Cooper               : 0.00
% 2.41/1.38  Total                : 0.59
% 2.41/1.38  Index Insertion      : 0.00
% 2.41/1.38  Index Deletion       : 0.00
% 2.41/1.38  Index Matching       : 0.00
% 2.41/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
