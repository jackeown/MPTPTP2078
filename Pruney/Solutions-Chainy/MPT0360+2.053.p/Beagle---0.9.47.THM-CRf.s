%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   48 (  84 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 ( 138 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_327,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_1'(A_70,B_71,C_72),B_71)
      | r2_hidden('#skF_2'(A_70,B_71,C_72),C_72)
      | k3_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_54])).

tff(c_82,plain,(
    ! [D_24,B_25,A_26] :
      ( r2_hidden(D_24,B_25)
      | ~ r2_hidden(D_24,k3_xboole_0(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_7')
      | ~ r2_hidden(D_24,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_82])).

tff(c_48,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_54])).

tff(c_85,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,k3_subset_1('#skF_5','#skF_7'))
      | ~ r2_hidden(D_24,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_82])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_208,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_208])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_235,plain,(
    ! [D_55] :
      ( ~ r2_hidden(D_55,'#skF_7')
      | ~ r2_hidden(D_55,k3_subset_1('#skF_5','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_22])).

tff(c_240,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,'#skF_7')
      | ~ r2_hidden(D_56,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_85,c_235])).

tff(c_244,plain,(
    ! [D_24] : ~ r2_hidden(D_24,'#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_240])).

tff(c_450,plain,(
    ! [A_73,C_74] :
      ( r2_hidden('#skF_2'(A_73,'#skF_6',C_74),C_74)
      | k3_xboole_0(A_73,'#skF_6') = C_74 ) ),
    inference(resolution,[status(thm)],[c_327,c_244])).

tff(c_516,plain,(
    ! [A_75] : k3_xboole_0(A_75,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_450,c_244])).

tff(c_42,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_533,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_65])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.51/1.37  
% 2.51/1.37  %Foreground sorts:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Background operators:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Foreground operators:
% 2.51/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.51/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.51/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.51/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.37  
% 2.51/1.38  tff(f_65, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.51/1.38  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.51/1.38  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.51/1.38  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.51/1.38  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.51/1.38  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.38  tff(c_46, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.38  tff(c_327, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_1'(A_70, B_71, C_72), B_71) | r2_hidden('#skF_2'(A_70, B_71, C_72), C_72) | k3_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.51/1.38  tff(c_50, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.38  tff(c_54, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.38  tff(c_66, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_50, c_54])).
% 2.51/1.38  tff(c_82, plain, (![D_24, B_25, A_26]: (r2_hidden(D_24, B_25) | ~r2_hidden(D_24, k3_xboole_0(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.51/1.38  tff(c_88, plain, (![D_24]: (r2_hidden(D_24, '#skF_7') | ~r2_hidden(D_24, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_82])).
% 2.51/1.38  tff(c_48, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.38  tff(c_64, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_48, c_54])).
% 2.51/1.38  tff(c_85, plain, (![D_24]: (r2_hidden(D_24, k3_subset_1('#skF_5', '#skF_7')) | ~r2_hidden(D_24, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_82])).
% 2.51/1.38  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.38  tff(c_208, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.38  tff(c_212, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_208])).
% 2.51/1.38  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.38  tff(c_235, plain, (![D_55]: (~r2_hidden(D_55, '#skF_7') | ~r2_hidden(D_55, k3_subset_1('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_212, c_22])).
% 2.51/1.38  tff(c_240, plain, (![D_56]: (~r2_hidden(D_56, '#skF_7') | ~r2_hidden(D_56, '#skF_6'))), inference(resolution, [status(thm)], [c_85, c_235])).
% 2.51/1.38  tff(c_244, plain, (![D_24]: (~r2_hidden(D_24, '#skF_6'))), inference(resolution, [status(thm)], [c_88, c_240])).
% 2.51/1.38  tff(c_450, plain, (![A_73, C_74]: (r2_hidden('#skF_2'(A_73, '#skF_6', C_74), C_74) | k3_xboole_0(A_73, '#skF_6')=C_74)), inference(resolution, [status(thm)], [c_327, c_244])).
% 2.51/1.38  tff(c_516, plain, (![A_75]: (k3_xboole_0(A_75, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_450, c_244])).
% 2.51/1.38  tff(c_42, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.38  tff(c_65, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.51/1.38  tff(c_533, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_516, c_65])).
% 2.51/1.38  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_533])).
% 2.51/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  Inference rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Ref     : 0
% 2.51/1.38  #Sup     : 134
% 2.51/1.38  #Fact    : 0
% 2.51/1.38  #Define  : 0
% 2.51/1.38  #Split   : 0
% 2.51/1.38  #Chain   : 0
% 2.51/1.38  #Close   : 0
% 2.51/1.38  
% 2.51/1.38  Ordering : KBO
% 2.51/1.38  
% 2.51/1.38  Simplification rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Subsume      : 40
% 2.51/1.38  #Demod        : 2
% 2.51/1.38  #Tautology    : 25
% 2.51/1.38  #SimpNegUnit  : 5
% 2.51/1.38  #BackRed      : 1
% 2.51/1.38  
% 2.51/1.38  #Partial instantiations: 0
% 2.51/1.38  #Strategies tried      : 1
% 2.51/1.38  
% 2.51/1.38  Timing (in seconds)
% 2.51/1.38  ----------------------
% 2.51/1.38  Preprocessing        : 0.29
% 2.51/1.38  Parsing              : 0.14
% 2.51/1.38  CNF conversion       : 0.02
% 2.51/1.38  Main loop            : 0.28
% 2.51/1.38  Inferencing          : 0.10
% 2.51/1.38  Reduction            : 0.08
% 2.51/1.38  Demodulation         : 0.06
% 2.51/1.38  BG Simplification    : 0.02
% 2.51/1.38  Subsumption          : 0.06
% 2.51/1.38  Abstraction          : 0.02
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.60
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
