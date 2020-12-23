%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:24 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  82 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_56,c_60])).

tff(c_127,plain,(
    ! [D_43,B_44,A_45] :
      ( r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k3_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_168,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_8')
      | ~ r2_hidden(D_48,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_127])).

tff(c_173,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'('#skF_7',B_2),'#skF_8')
      | r1_tarski('#skF_7',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_168])).

tff(c_54,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_67,plain,(
    k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_8')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_60])).

tff(c_134,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,k3_subset_1('#skF_6','#skF_8'))
      | ~ r2_hidden(D_43,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_127])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_240,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_244,plain,(
    k4_xboole_0('#skF_6','#skF_8') = k3_subset_1('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_240])).

tff(c_28,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_255,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,'#skF_8')
      | ~ r2_hidden(D_58,k3_subset_1('#skF_6','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_28])).

tff(c_265,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,'#skF_8')
      | ~ r2_hidden(D_59,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_134,c_255])).

tff(c_287,plain,(
    ! [B_62] :
      ( ~ r2_hidden('#skF_1'('#skF_7',B_62),'#skF_8')
      | r1_tarski('#skF_7',B_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_265])).

tff(c_296,plain,(
    ! [B_63] : r1_tarski('#skF_7',B_63) ),
    inference(resolution,[status(thm)],[c_173,c_287])).

tff(c_48,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_296,c_48])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:49:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 2.03/1.30  
% 2.03/1.30  %Foreground sorts:
% 2.03/1.30  
% 2.03/1.30  
% 2.03/1.30  %Background operators:
% 2.03/1.30  
% 2.03/1.30  
% 2.03/1.30  %Foreground operators:
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.03/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.03/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.03/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.30  
% 2.03/1.31  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.03/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.31  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.03/1.31  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.03/1.31  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.03/1.31  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.03/1.31  tff(f_61, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.03/1.31  tff(c_52, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.03/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.31  tff(c_56, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.03/1.31  tff(c_60, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.31  tff(c_68, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_56, c_60])).
% 2.03/1.31  tff(c_127, plain, (![D_43, B_44, A_45]: (r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k3_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.31  tff(c_168, plain, (![D_48]: (r2_hidden(D_48, '#skF_8') | ~r2_hidden(D_48, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_127])).
% 2.03/1.31  tff(c_173, plain, (![B_2]: (r2_hidden('#skF_1'('#skF_7', B_2), '#skF_8') | r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_6, c_168])).
% 2.03/1.31  tff(c_54, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.03/1.31  tff(c_67, plain, (k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_8'))='#skF_7'), inference(resolution, [status(thm)], [c_54, c_60])).
% 2.03/1.31  tff(c_134, plain, (![D_43]: (r2_hidden(D_43, k3_subset_1('#skF_6', '#skF_8')) | ~r2_hidden(D_43, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_127])).
% 2.03/1.31  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.03/1.31  tff(c_240, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.31  tff(c_244, plain, (k4_xboole_0('#skF_6', '#skF_8')=k3_subset_1('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_58, c_240])).
% 2.03/1.31  tff(c_28, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.31  tff(c_255, plain, (![D_58]: (~r2_hidden(D_58, '#skF_8') | ~r2_hidden(D_58, k3_subset_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_244, c_28])).
% 2.03/1.31  tff(c_265, plain, (![D_59]: (~r2_hidden(D_59, '#skF_8') | ~r2_hidden(D_59, '#skF_7'))), inference(resolution, [status(thm)], [c_134, c_255])).
% 2.03/1.31  tff(c_287, plain, (![B_62]: (~r2_hidden('#skF_1'('#skF_7', B_62), '#skF_8') | r1_tarski('#skF_7', B_62))), inference(resolution, [status(thm)], [c_6, c_265])).
% 2.03/1.31  tff(c_296, plain, (![B_63]: (r1_tarski('#skF_7', B_63))), inference(resolution, [status(thm)], [c_173, c_287])).
% 2.03/1.31  tff(c_48, plain, (![A_22]: (k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.31  tff(c_303, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_296, c_48])).
% 2.03/1.31  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_303])).
% 2.03/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.31  
% 2.03/1.31  Inference rules
% 2.03/1.31  ----------------------
% 2.03/1.31  #Ref     : 0
% 2.03/1.31  #Sup     : 61
% 2.03/1.31  #Fact    : 0
% 2.03/1.31  #Define  : 0
% 2.03/1.31  #Split   : 0
% 2.03/1.31  #Chain   : 0
% 2.03/1.31  #Close   : 0
% 2.03/1.31  
% 2.03/1.31  Ordering : KBO
% 2.03/1.31  
% 2.03/1.31  Simplification rules
% 2.03/1.31  ----------------------
% 2.03/1.31  #Subsume      : 2
% 2.03/1.31  #Demod        : 7
% 2.03/1.31  #Tautology    : 29
% 2.03/1.31  #SimpNegUnit  : 1
% 2.03/1.31  #BackRed      : 0
% 2.03/1.31  
% 2.03/1.31  #Partial instantiations: 0
% 2.03/1.31  #Strategies tried      : 1
% 2.03/1.31  
% 2.03/1.31  Timing (in seconds)
% 2.03/1.31  ----------------------
% 2.03/1.32  Preprocessing        : 0.34
% 2.03/1.32  Parsing              : 0.17
% 2.03/1.32  CNF conversion       : 0.03
% 2.03/1.32  Main loop            : 0.21
% 2.03/1.32  Inferencing          : 0.07
% 2.03/1.32  Reduction            : 0.06
% 2.03/1.32  Demodulation         : 0.04
% 2.03/1.32  BG Simplification    : 0.02
% 2.03/1.32  Subsumption          : 0.04
% 2.03/1.32  Abstraction          : 0.01
% 2.03/1.32  MUC search           : 0.00
% 2.03/1.32  Cooper               : 0.00
% 2.03/1.32  Total                : 0.57
% 2.03/1.32  Index Insertion      : 0.00
% 2.03/1.32  Index Deletion       : 0.00
% 2.03/1.32  Index Matching       : 0.00
% 2.03/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
