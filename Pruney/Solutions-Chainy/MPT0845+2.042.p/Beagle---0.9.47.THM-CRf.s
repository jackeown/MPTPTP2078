%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  74 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_66,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_68,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

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

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_59)
      | r2_hidden('#skF_2'(A_58,B_59),A_58)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_512,plain,(
    ! [A_83,B_84,A_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | r2_hidden('#skF_2'(A_85,k3_xboole_0(A_83,B_84)),A_85)
      | k3_xboole_0(A_83,B_84) = A_85 ) ),
    inference(resolution,[status(thm)],[c_152,c_18])).

tff(c_544,plain,(
    ! [A_14,A_85] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | r2_hidden('#skF_2'(A_85,k1_xboole_0),A_85)
      | k3_xboole_0(A_14,k1_xboole_0) = A_85 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_512])).

tff(c_553,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_2'(A_85,k1_xboole_0),A_85)
      | k1_xboole_0 = A_85 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_544])).

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

tff(c_135,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,'#skF_5'(A_54,B_55))
      | ~ r2_hidden(D_53,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_585,plain,(
    ! [A_87,B_88,B_89] :
      ( ~ r2_hidden('#skF_3'('#skF_5'(A_87,B_88),B_89),B_88)
      | ~ r2_hidden(A_87,B_88)
      | r1_xboole_0('#skF_5'(A_87,B_88),B_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_591,plain,(
    ! [A_90,B_91] :
      ( ~ r2_hidden(A_90,B_91)
      | r1_xboole_0('#skF_5'(A_90,B_91),B_91) ) ),
    inference(resolution,[status(thm)],[c_12,c_585])).

tff(c_82,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_5'(A_38,B_39),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [B_24] :
      ( ~ r1_xboole_0(B_24,'#skF_6')
      | ~ r2_hidden(B_24,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_97,plain,(
    ! [A_38] :
      ( ~ r1_xboole_0('#skF_5'(A_38,'#skF_6'),'#skF_6')
      | ~ r2_hidden(A_38,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_28])).

tff(c_607,plain,(
    ! [A_92] : ~ r2_hidden(A_92,'#skF_6') ),
    inference(resolution,[status(thm)],[c_591,c_97])).

tff(c_611,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_553,c_607])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.39  
% 2.48/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.39  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.48/1.39  
% 2.48/1.39  %Foreground sorts:
% 2.48/1.39  
% 2.48/1.39  
% 2.48/1.39  %Background operators:
% 2.48/1.39  
% 2.48/1.39  
% 2.48/1.39  %Foreground operators:
% 2.48/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.39  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.48/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.48/1.39  
% 2.48/1.40  tff(f_92, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.48/1.40  tff(f_66, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.48/1.40  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.48/1.40  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.48/1.40  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.48/1.40  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.48/1.40  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.48/1.40  tff(c_30, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.48/1.40  tff(c_20, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.48/1.40  tff(c_22, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.48/1.40  tff(c_152, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), B_59) | r2_hidden('#skF_2'(A_58, B_59), A_58) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.40  tff(c_18, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.48/1.40  tff(c_512, plain, (![A_83, B_84, A_85]: (~r1_xboole_0(A_83, B_84) | r2_hidden('#skF_2'(A_85, k3_xboole_0(A_83, B_84)), A_85) | k3_xboole_0(A_83, B_84)=A_85)), inference(resolution, [status(thm)], [c_152, c_18])).
% 2.48/1.40  tff(c_544, plain, (![A_14, A_85]: (~r1_xboole_0(A_14, k1_xboole_0) | r2_hidden('#skF_2'(A_85, k1_xboole_0), A_85) | k3_xboole_0(A_14, k1_xboole_0)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_20, c_512])).
% 2.48/1.40  tff(c_553, plain, (![A_85]: (r2_hidden('#skF_2'(A_85, k1_xboole_0), A_85) | k1_xboole_0=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_544])).
% 2.48/1.40  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.48/1.40  tff(c_14, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.48/1.40  tff(c_135, plain, (![D_53, A_54, B_55]: (~r2_hidden(D_53, '#skF_5'(A_54, B_55)) | ~r2_hidden(D_53, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.48/1.40  tff(c_585, plain, (![A_87, B_88, B_89]: (~r2_hidden('#skF_3'('#skF_5'(A_87, B_88), B_89), B_88) | ~r2_hidden(A_87, B_88) | r1_xboole_0('#skF_5'(A_87, B_88), B_89))), inference(resolution, [status(thm)], [c_14, c_135])).
% 2.48/1.40  tff(c_591, plain, (![A_90, B_91]: (~r2_hidden(A_90, B_91) | r1_xboole_0('#skF_5'(A_90, B_91), B_91))), inference(resolution, [status(thm)], [c_12, c_585])).
% 2.48/1.40  tff(c_82, plain, (![A_38, B_39]: (r2_hidden('#skF_5'(A_38, B_39), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.48/1.40  tff(c_28, plain, (![B_24]: (~r1_xboole_0(B_24, '#skF_6') | ~r2_hidden(B_24, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.48/1.40  tff(c_97, plain, (![A_38]: (~r1_xboole_0('#skF_5'(A_38, '#skF_6'), '#skF_6') | ~r2_hidden(A_38, '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_28])).
% 2.48/1.40  tff(c_607, plain, (![A_92]: (~r2_hidden(A_92, '#skF_6'))), inference(resolution, [status(thm)], [c_591, c_97])).
% 2.48/1.40  tff(c_611, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_553, c_607])).
% 2.48/1.40  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_611])).
% 2.48/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.40  
% 2.48/1.40  Inference rules
% 2.48/1.40  ----------------------
% 2.48/1.40  #Ref     : 0
% 2.48/1.40  #Sup     : 128
% 2.48/1.40  #Fact    : 0
% 2.48/1.40  #Define  : 0
% 2.48/1.40  #Split   : 0
% 2.48/1.40  #Chain   : 0
% 2.48/1.40  #Close   : 0
% 2.48/1.40  
% 2.48/1.40  Ordering : KBO
% 2.48/1.40  
% 2.48/1.40  Simplification rules
% 2.48/1.40  ----------------------
% 2.48/1.40  #Subsume      : 31
% 2.48/1.40  #Demod        : 42
% 2.48/1.40  #Tautology    : 46
% 2.48/1.40  #SimpNegUnit  : 9
% 2.48/1.40  #BackRed      : 0
% 2.48/1.40  
% 2.48/1.40  #Partial instantiations: 0
% 2.48/1.40  #Strategies tried      : 1
% 2.48/1.40  
% 2.48/1.40  Timing (in seconds)
% 2.48/1.40  ----------------------
% 2.48/1.40  Preprocessing        : 0.31
% 2.48/1.40  Parsing              : 0.17
% 2.48/1.40  CNF conversion       : 0.03
% 2.48/1.40  Main loop            : 0.27
% 2.48/1.40  Inferencing          : 0.12
% 2.48/1.40  Reduction            : 0.07
% 2.48/1.40  Demodulation         : 0.05
% 2.48/1.40  BG Simplification    : 0.01
% 2.48/1.40  Subsumption          : 0.05
% 2.48/1.40  Abstraction          : 0.01
% 2.48/1.40  MUC search           : 0.00
% 2.48/1.40  Cooper               : 0.00
% 2.48/1.40  Total                : 0.61
% 2.48/1.40  Index Insertion      : 0.00
% 2.48/1.40  Index Deletion       : 0.00
% 2.48/1.40  Index Matching       : 0.00
% 2.48/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
