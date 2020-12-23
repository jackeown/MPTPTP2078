%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  66 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ( r1_tarski(A,D)
         => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_59,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [B_25,A_26] :
      ( r2_hidden(B_25,A_26)
      | ~ m1_subset_1(B_25,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [B_25,A_6] :
      ( r1_tarski(B_25,A_6)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_59,c_6])).

tff(c_71,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(B_27,A_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_63])).

tff(c_80,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_105,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_37,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_105])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [B_29,A_30] :
      ( m1_subset_1(B_29,A_30)
      | ~ r2_hidden(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_87,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_92,plain,(
    ! [C_31,A_32] :
      ( m1_subset_1(C_31,k1_zfmisc_1(A_32))
      | ~ r1_tarski(C_31,A_32) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_87])).

tff(c_28,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_92,c_28])).

tff(c_121,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_104])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.16  
% 1.83/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.83/1.16  
% 1.83/1.16  %Foreground sorts:
% 1.83/1.16  
% 1.83/1.16  
% 1.83/1.16  %Background operators:
% 1.83/1.16  
% 1.83/1.16  
% 1.83/1.16  %Foreground operators:
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.83/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.16  
% 1.83/1.17  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 1.83/1.17  tff(f_59, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.83/1.17  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.83/1.17  tff(f_43, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.83/1.17  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.83/1.17  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.83/1.17  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.83/1.17  tff(c_26, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.83/1.17  tff(c_59, plain, (![B_25, A_26]: (r2_hidden(B_25, A_26) | ~m1_subset_1(B_25, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.17  tff(c_6, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.17  tff(c_63, plain, (![B_25, A_6]: (r1_tarski(B_25, A_6) | ~m1_subset_1(B_25, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_59, c_6])).
% 1.83/1.17  tff(c_71, plain, (![B_27, A_28]: (r1_tarski(B_27, A_28) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)))), inference(negUnitSimplification, [status(thm)], [c_26, c_63])).
% 1.83/1.17  tff(c_80, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_71])).
% 1.83/1.17  tff(c_105, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.17  tff(c_116, plain, (![A_37]: (r1_tarski(A_37, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_37, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_105])).
% 1.83/1.17  tff(c_8, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.17  tff(c_81, plain, (![B_29, A_30]: (m1_subset_1(B_29, A_30) | ~r2_hidden(B_29, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.17  tff(c_87, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_8, c_81])).
% 1.83/1.17  tff(c_92, plain, (![C_31, A_32]: (m1_subset_1(C_31, k1_zfmisc_1(A_32)) | ~r1_tarski(C_31, A_32))), inference(negUnitSimplification, [status(thm)], [c_26, c_87])).
% 1.83/1.17  tff(c_28, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.83/1.17  tff(c_104, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_28])).
% 1.83/1.17  tff(c_121, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_116, c_104])).
% 1.83/1.17  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_121])).
% 1.83/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  Inference rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Ref     : 0
% 1.83/1.17  #Sup     : 19
% 1.83/1.17  #Fact    : 0
% 1.83/1.17  #Define  : 0
% 1.83/1.17  #Split   : 0
% 1.83/1.17  #Chain   : 0
% 1.83/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 5
% 1.83/1.17  #Demod        : 1
% 1.83/1.17  #Tautology    : 5
% 1.83/1.17  #SimpNegUnit  : 2
% 1.83/1.17  #BackRed      : 0
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.17  Preprocessing        : 0.27
% 1.83/1.17  Parsing              : 0.15
% 1.83/1.17  CNF conversion       : 0.02
% 1.83/1.17  Main loop            : 0.14
% 1.83/1.17  Inferencing          : 0.06
% 1.83/1.18  Reduction            : 0.04
% 1.83/1.18  Demodulation         : 0.02
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.03
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.44
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
