%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   46 (  83 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 130 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(k2_tarski(A_37,B_38),C_39)
      | ~ r2_hidden(B_38,C_39)
      | ~ r2_hidden(A_37,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [A_1,C_39] :
      ( r1_tarski(k1_tarski(A_1),C_39)
      | ~ r2_hidden(A_1,C_39)
      | ~ r2_hidden(A_1,C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r1_tarski(k2_zfmisc_1(A_7,C_9),k2_zfmisc_1(B_8,D_10))
      | ~ r1_tarski(C_9,D_10)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_46,B_47,C_48] : k2_zfmisc_1(k2_tarski(A_46,B_47),k1_tarski(C_48)) = k2_tarski(k4_tarski(A_46,C_48),k4_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [B_15,C_16,A_14] :
      ( r2_hidden(B_15,C_16)
      | ~ r1_tarski(k2_tarski(A_14,B_15),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_291,plain,(
    ! [B_66,C_67,C_68,A_69] :
      ( r2_hidden(k4_tarski(B_66,C_67),C_68)
      | ~ r1_tarski(k2_zfmisc_1(k2_tarski(A_69,B_66),k1_tarski(C_67)),C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_16])).

tff(c_362,plain,(
    ! [C_81,D_78,B_79,B_82,A_80] :
      ( r2_hidden(k4_tarski(B_82,C_81),k2_zfmisc_1(B_79,D_78))
      | ~ r1_tarski(k1_tarski(C_81),D_78)
      | ~ r1_tarski(k2_tarski(A_80,B_82),B_79) ) ),
    inference(resolution,[status(thm)],[c_8,c_291])).

tff(c_372,plain,(
    ! [A_83,C_84,B_85,D_86] :
      ( r2_hidden(k4_tarski(A_83,C_84),k2_zfmisc_1(B_85,D_86))
      | ~ r1_tarski(k1_tarski(C_84),D_86)
      | ~ r1_tarski(k1_tarski(A_83),B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_362])).

tff(c_87,plain,(
    ! [A_40,C_41] :
      ( r1_tarski(k1_tarski(A_40),C_41)
      | ~ r2_hidden(A_40,C_41)
      | ~ r2_hidden(A_40,C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_65,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_24])).

tff(c_94,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_87,c_65])).

tff(c_385,plain,
    ( ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_372,c_94])).

tff(c_386,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_389,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_389])).

tff(c_394,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_398,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_394])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.33  
% 2.33/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.33/1.33  
% 2.33/1.33  %Foreground sorts:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Background operators:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Foreground operators:
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.33  
% 2.33/1.34  tff(f_58, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 2.33/1.34  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.33/1.34  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.33/1.34  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.33/1.34  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.33/1.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.34  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.34  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.34  tff(c_75, plain, (![A_37, B_38, C_39]: (r1_tarski(k2_tarski(A_37, B_38), C_39) | ~r2_hidden(B_38, C_39) | ~r2_hidden(A_37, C_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.34  tff(c_84, plain, (![A_1, C_39]: (r1_tarski(k1_tarski(A_1), C_39) | ~r2_hidden(A_1, C_39) | ~r2_hidden(A_1, C_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 2.33/1.34  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.34  tff(c_8, plain, (![A_7, C_9, B_8, D_10]: (r1_tarski(k2_zfmisc_1(A_7, C_9), k2_zfmisc_1(B_8, D_10)) | ~r1_tarski(C_9, D_10) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.34  tff(c_97, plain, (![A_46, B_47, C_48]: (k2_zfmisc_1(k2_tarski(A_46, B_47), k1_tarski(C_48))=k2_tarski(k4_tarski(A_46, C_48), k4_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.34  tff(c_16, plain, (![B_15, C_16, A_14]: (r2_hidden(B_15, C_16) | ~r1_tarski(k2_tarski(A_14, B_15), C_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.34  tff(c_291, plain, (![B_66, C_67, C_68, A_69]: (r2_hidden(k4_tarski(B_66, C_67), C_68) | ~r1_tarski(k2_zfmisc_1(k2_tarski(A_69, B_66), k1_tarski(C_67)), C_68))), inference(superposition, [status(thm), theory('equality')], [c_97, c_16])).
% 2.33/1.34  tff(c_362, plain, (![C_81, D_78, B_79, B_82, A_80]: (r2_hidden(k4_tarski(B_82, C_81), k2_zfmisc_1(B_79, D_78)) | ~r1_tarski(k1_tarski(C_81), D_78) | ~r1_tarski(k2_tarski(A_80, B_82), B_79))), inference(resolution, [status(thm)], [c_8, c_291])).
% 2.33/1.34  tff(c_372, plain, (![A_83, C_84, B_85, D_86]: (r2_hidden(k4_tarski(A_83, C_84), k2_zfmisc_1(B_85, D_86)) | ~r1_tarski(k1_tarski(C_84), D_86) | ~r1_tarski(k1_tarski(A_83), B_85))), inference(superposition, [status(thm), theory('equality')], [c_2, c_362])).
% 2.33/1.34  tff(c_87, plain, (![A_40, C_41]: (r1_tarski(k1_tarski(A_40), C_41) | ~r2_hidden(A_40, C_41) | ~r2_hidden(A_40, C_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 2.33/1.34  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.33/1.34  tff(c_24, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.34  tff(c_65, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_24])).
% 2.33/1.34  tff(c_94, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_87, c_65])).
% 2.33/1.34  tff(c_385, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_372, c_94])).
% 2.33/1.34  tff(c_386, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_385])).
% 2.33/1.34  tff(c_389, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_386])).
% 2.33/1.34  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_389])).
% 2.33/1.34  tff(c_394, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_385])).
% 2.33/1.34  tff(c_398, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_394])).
% 2.33/1.34  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_398])).
% 2.33/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  Inference rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Ref     : 0
% 2.33/1.34  #Sup     : 94
% 2.33/1.34  #Fact    : 0
% 2.33/1.34  #Define  : 0
% 2.33/1.34  #Split   : 1
% 2.33/1.34  #Chain   : 0
% 2.33/1.34  #Close   : 0
% 2.33/1.34  
% 2.33/1.34  Ordering : KBO
% 2.33/1.34  
% 2.33/1.34  Simplification rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Subsume      : 11
% 2.33/1.34  #Demod        : 22
% 2.33/1.34  #Tautology    : 29
% 2.33/1.34  #SimpNegUnit  : 0
% 2.33/1.34  #BackRed      : 0
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.35  Preprocessing        : 0.31
% 2.33/1.35  Parsing              : 0.16
% 2.33/1.35  CNF conversion       : 0.02
% 2.33/1.35  Main loop            : 0.27
% 2.33/1.35  Inferencing          : 0.10
% 2.33/1.35  Reduction            : 0.08
% 2.33/1.35  Demodulation         : 0.06
% 2.33/1.35  BG Simplification    : 0.02
% 2.33/1.35  Subsumption          : 0.05
% 2.33/1.35  Abstraction          : 0.02
% 2.33/1.35  MUC search           : 0.00
% 2.33/1.35  Cooper               : 0.00
% 2.33/1.35  Total                : 0.60
% 2.33/1.35  Index Insertion      : 0.00
% 2.33/1.35  Index Deletion       : 0.00
% 2.33/1.35  Index Matching       : 0.00
% 2.33/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
