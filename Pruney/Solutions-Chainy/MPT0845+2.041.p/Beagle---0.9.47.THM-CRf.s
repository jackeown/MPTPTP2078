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
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  63 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_50,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_134,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r2_hidden('#skF_2'(A_47,B_48),A_47)
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_53,plain,(
    ! [A_24,B_25] : ~ r2_hidden(A_24,k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_53])).

tff(c_158,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_48),B_48)
      | k1_xboole_0 = B_48 ) ),
    inference(resolution,[status(thm)],[c_134,c_56])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [D_44,A_45,B_46] :
      ( ~ r2_hidden(D_44,'#skF_4'(A_45,B_46))
      | ~ r2_hidden(D_44,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_248,plain,(
    ! [A_65,B_66,B_67] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_65,B_66),B_67),B_66)
      | ~ r2_hidden(A_65,B_66)
      | r1_xboole_0('#skF_4'(A_65,B_66),B_67) ) ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_254,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden(A_68,B_69)
      | r1_xboole_0('#skF_4'(A_68,B_69),B_69) ) ),
    inference(resolution,[status(thm)],[c_12,c_248])).

tff(c_73,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_4'(A_30,B_31),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [B_21] :
      ( ~ r1_xboole_0(B_21,'#skF_5')
      | ~ r2_hidden(B_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_82,plain,(
    ! [A_30] :
      ( ~ r1_xboole_0('#skF_4'(A_30,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_30,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_73,c_28])).

tff(c_263,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_5') ),
    inference(resolution,[status(thm)],[c_254,c_82])).

tff(c_271,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_158,c_263])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  %$ r2_hidden > r1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.99/1.24  
% 1.99/1.25  tff(f_83, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 1.99/1.25  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.99/1.25  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.99/1.25  tff(f_59, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.99/1.25  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.99/1.25  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 1.99/1.25  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.25  tff(c_134, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), B_48) | r2_hidden('#skF_2'(A_47, B_48), A_47) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.25  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.25  tff(c_53, plain, (![A_24, B_25]: (~r2_hidden(A_24, k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.25  tff(c_56, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_53])).
% 1.99/1.25  tff(c_158, plain, (![B_48]: (r2_hidden('#skF_1'(k1_xboole_0, B_48), B_48) | k1_xboole_0=B_48)), inference(resolution, [status(thm)], [c_134, c_56])).
% 1.99/1.25  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.25  tff(c_14, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.25  tff(c_118, plain, (![D_44, A_45, B_46]: (~r2_hidden(D_44, '#skF_4'(A_45, B_46)) | ~r2_hidden(D_44, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.25  tff(c_248, plain, (![A_65, B_66, B_67]: (~r2_hidden('#skF_3'('#skF_4'(A_65, B_66), B_67), B_66) | ~r2_hidden(A_65, B_66) | r1_xboole_0('#skF_4'(A_65, B_66), B_67))), inference(resolution, [status(thm)], [c_14, c_118])).
% 1.99/1.25  tff(c_254, plain, (![A_68, B_69]: (~r2_hidden(A_68, B_69) | r1_xboole_0('#skF_4'(A_68, B_69), B_69))), inference(resolution, [status(thm)], [c_12, c_248])).
% 1.99/1.25  tff(c_73, plain, (![A_30, B_31]: (r2_hidden('#skF_4'(A_30, B_31), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.25  tff(c_28, plain, (![B_21]: (~r1_xboole_0(B_21, '#skF_5') | ~r2_hidden(B_21, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.25  tff(c_82, plain, (![A_30]: (~r1_xboole_0('#skF_4'(A_30, '#skF_5'), '#skF_5') | ~r2_hidden(A_30, '#skF_5'))), inference(resolution, [status(thm)], [c_73, c_28])).
% 1.99/1.25  tff(c_263, plain, (![A_70]: (~r2_hidden(A_70, '#skF_5'))), inference(resolution, [status(thm)], [c_254, c_82])).
% 1.99/1.25  tff(c_271, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_158, c_263])).
% 1.99/1.25  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_271])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 49
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 0
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 12
% 1.99/1.25  #Demod        : 0
% 1.99/1.25  #Tautology    : 13
% 1.99/1.25  #SimpNegUnit  : 3
% 1.99/1.25  #BackRed      : 0
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 2.11/1.25  Preprocessing        : 0.29
% 2.11/1.25  Parsing              : 0.15
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.20
% 2.11/1.25  Inferencing          : 0.09
% 2.11/1.26  Reduction            : 0.05
% 2.11/1.26  Demodulation         : 0.03
% 2.11/1.26  BG Simplification    : 0.01
% 2.11/1.26  Subsumption          : 0.04
% 2.11/1.26  Abstraction          : 0.01
% 2.11/1.26  MUC search           : 0.00
% 2.11/1.26  Cooper               : 0.00
% 2.11/1.26  Total                : 0.51
% 2.11/1.26  Index Insertion      : 0.00
% 2.11/1.26  Index Deletion       : 0.00
% 2.11/1.26  Index Matching       : 0.00
% 2.11/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
