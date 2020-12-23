%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:39 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   38 (  70 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 145 expanded)
%              Number of equality atoms :   17 (  86 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_12,plain,
    ( k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_18,plain,
    ( k1_xboole_0 != '#skF_2'
    | k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    k7_setfam_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_27,c_18])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_29,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_2])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k7_setfam_1(A_11,B_12),C_13)
      | ~ r1_tarski(B_12,k7_setfam_1(A_11,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [B_14] :
      ( r1_tarski(k7_setfam_1('#skF_1',B_14),'#skF_2')
      | ~ r1_tarski(B_14,k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_51,plain,
    ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_54,plain,(
    r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_51])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_2] :
      ( A_2 = '#skF_2'
      | ~ r1_tarski(A_2,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_27,c_4])).

tff(c_57,plain,(
    k7_setfam_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_28])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_57])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_62,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_70,plain,(
    ! [B_15,A_16,C_17] :
      ( r1_tarski(B_15,k7_setfam_1(A_16,C_17))
      | ~ r1_tarski(k7_setfam_1(A_16,B_15),C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k1_zfmisc_1(A_16)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [C_17] :
      ( r1_tarski('#skF_2',k7_setfam_1('#skF_1',C_17))
      | ~ r1_tarski(k1_xboole_0,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_70])).

tff(c_80,plain,(
    ! [C_21] :
      ( r1_tarski('#skF_2',k7_setfam_1('#skF_1',C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2,c_72])).

tff(c_83,plain,(
    r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_85,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_83])).

tff(c_88,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.11  %$ r1_tarski > m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.11  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.66/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.11  
% 1.74/1.12  tff(f_55, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 1.74/1.12  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.74/1.12  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_setfam_1)).
% 1.74/1.12  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.74/1.12  tff(c_12, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.12  tff(c_27, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_12])).
% 1.74/1.12  tff(c_18, plain, (k1_xboole_0!='#skF_2' | k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.12  tff(c_43, plain, (k7_setfam_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27, c_27, c_18])).
% 1.74/1.12  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.12  tff(c_29, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_2])).
% 1.74/1.12  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.12  tff(c_44, plain, (![A_11, B_12, C_13]: (r1_tarski(k7_setfam_1(A_11, B_12), C_13) | ~r1_tarski(B_12, k7_setfam_1(A_11, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(k1_zfmisc_1(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.12  tff(c_48, plain, (![B_14]: (r1_tarski(k7_setfam_1('#skF_1', B_14), '#skF_2') | ~r1_tarski(B_14, k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_10, c_44])).
% 1.74/1.12  tff(c_51, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_48])).
% 1.74/1.12  tff(c_54, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_51])).
% 1.74/1.12  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.12  tff(c_28, plain, (![A_2]: (A_2='#skF_2' | ~r1_tarski(A_2, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_27, c_4])).
% 1.74/1.12  tff(c_57, plain, (k7_setfam_1('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_54, c_28])).
% 1.74/1.12  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_57])).
% 1.74/1.12  tff(c_63, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_12])).
% 1.74/1.12  tff(c_62, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 1.74/1.12  tff(c_70, plain, (![B_15, A_16, C_17]: (r1_tarski(B_15, k7_setfam_1(A_16, C_17)) | ~r1_tarski(k7_setfam_1(A_16, B_15), C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k1_zfmisc_1(A_16))) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.12  tff(c_72, plain, (![C_17]: (r1_tarski('#skF_2', k7_setfam_1('#skF_1', C_17)) | ~r1_tarski(k1_xboole_0, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_62, c_70])).
% 1.74/1.12  tff(c_80, plain, (![C_21]: (r1_tarski('#skF_2', k7_setfam_1('#skF_1', C_21)) | ~m1_subset_1(C_21, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2, c_72])).
% 1.74/1.12  tff(c_83, plain, (r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_80])).
% 1.74/1.12  tff(c_85, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_83])).
% 1.74/1.12  tff(c_88, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_85, c_4])).
% 1.74/1.12  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_88])).
% 1.74/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.12  
% 1.74/1.12  Inference rules
% 1.74/1.12  ----------------------
% 1.74/1.12  #Ref     : 0
% 1.74/1.12  #Sup     : 13
% 1.74/1.12  #Fact    : 0
% 1.74/1.12  #Define  : 0
% 1.74/1.12  #Split   : 1
% 1.74/1.12  #Chain   : 0
% 1.74/1.12  #Close   : 0
% 1.74/1.12  
% 1.74/1.12  Ordering : KBO
% 1.74/1.12  
% 1.74/1.12  Simplification rules
% 1.74/1.12  ----------------------
% 1.74/1.12  #Subsume      : 1
% 1.74/1.12  #Demod        : 11
% 1.74/1.12  #Tautology    : 8
% 1.74/1.12  #SimpNegUnit  : 2
% 1.74/1.12  #BackRed      : 2
% 1.74/1.12  
% 1.74/1.12  #Partial instantiations: 0
% 1.74/1.12  #Strategies tried      : 1
% 1.74/1.12  
% 1.74/1.12  Timing (in seconds)
% 1.74/1.12  ----------------------
% 1.74/1.12  Preprocessing        : 0.26
% 1.74/1.12  Parsing              : 0.14
% 1.74/1.12  CNF conversion       : 0.02
% 1.74/1.12  Main loop            : 0.10
% 1.74/1.12  Inferencing          : 0.04
% 1.74/1.12  Reduction            : 0.03
% 1.74/1.12  Demodulation         : 0.02
% 1.74/1.12  BG Simplification    : 0.01
% 1.74/1.12  Subsumption          : 0.02
% 1.74/1.12  Abstraction          : 0.00
% 1.74/1.12  MUC search           : 0.00
% 1.74/1.12  Cooper               : 0.00
% 1.74/1.12  Total                : 0.39
% 1.74/1.12  Index Insertion      : 0.00
% 1.74/1.12  Index Deletion       : 0.00
% 1.74/1.12  Index Matching       : 0.00
% 1.74/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
