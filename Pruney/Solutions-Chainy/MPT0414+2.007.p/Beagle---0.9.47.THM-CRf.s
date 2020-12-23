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
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   42 (  95 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 282 expanded)
%              Number of equality atoms :    5 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_1'(A_34,B_35,C_36),B_35)
      | r1_tarski(B_35,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_23,C_24,B_25] :
      ( m1_subset_1(A_23,C_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_24,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_4')
      | ~ r2_hidden(D_17,'#skF_3')
      | ~ m1_subset_1(D_17,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ! [A_28] :
      ( r2_hidden(A_28,'#skF_4')
      | ~ r2_hidden(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_24])).

tff(c_89,plain,(
    ! [A_34,C_36] :
      ( r2_hidden('#skF_1'(A_34,'#skF_3',C_36),'#skF_4')
      | r1_tarski('#skF_3',C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_78,c_63])).

tff(c_101,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40,C_41),C_41)
      | r1_tarski(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_34] :
      ( r1_tarski('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_89,c_101])).

tff(c_119,plain,(
    ! [A_42] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_42))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_42)) ) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_130,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_137,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_142,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_139])).

tff(c_10,plain,(
    ! [A_3,B_4,C_8] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_8),B_4)
      | r1_tarski(B_4,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_26] :
      ( m1_subset_1(A_26,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_26,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_22,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_3')
      | ~ r2_hidden(D_17,'#skF_4')
      | ~ m1_subset_1(D_17,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [A_26] :
      ( r2_hidden(A_26,'#skF_3')
      | ~ r2_hidden(A_26,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_22])).

tff(c_148,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ r2_hidden('#skF_1'(A_47,B_46,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_156,plain,(
    ! [A_3] :
      ( r1_tarski('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_162,plain,(
    ! [A_48] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_48))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_48)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_142,c_156])).

tff(c_173,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.32  
% 1.96/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.96/1.33  
% 1.96/1.33  %Foreground sorts:
% 1.96/1.33  
% 1.96/1.33  
% 1.96/1.33  %Background operators:
% 1.96/1.33  
% 1.96/1.33  
% 1.96/1.33  %Foreground operators:
% 1.96/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.33  
% 2.15/1.34  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.15/1.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.15/1.34  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.15/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.15/1.34  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.34  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.34  tff(c_16, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.34  tff(c_78, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_1'(A_34, B_35, C_36), B_35) | r1_tarski(B_35, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.34  tff(c_36, plain, (![A_23, C_24, B_25]: (m1_subset_1(A_23, C_24) | ~m1_subset_1(B_25, k1_zfmisc_1(C_24)) | ~r2_hidden(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.34  tff(c_56, plain, (![A_28]: (m1_subset_1(A_28, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_36])).
% 2.15/1.34  tff(c_24, plain, (![D_17]: (r2_hidden(D_17, '#skF_4') | ~r2_hidden(D_17, '#skF_3') | ~m1_subset_1(D_17, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.34  tff(c_63, plain, (![A_28]: (r2_hidden(A_28, '#skF_4') | ~r2_hidden(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_24])).
% 2.15/1.34  tff(c_89, plain, (![A_34, C_36]: (r2_hidden('#skF_1'(A_34, '#skF_3', C_36), '#skF_4') | r1_tarski('#skF_3', C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_34)))), inference(resolution, [status(thm)], [c_78, c_63])).
% 2.15/1.34  tff(c_101, plain, (![A_39, B_40, C_41]: (~r2_hidden('#skF_1'(A_39, B_40, C_41), C_41) | r1_tarski(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.34  tff(c_114, plain, (![A_34]: (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_34)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_34)))), inference(resolution, [status(thm)], [c_89, c_101])).
% 2.15/1.34  tff(c_119, plain, (![A_42]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_42)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_42)))), inference(splitLeft, [status(thm)], [c_114])).
% 2.15/1.34  tff(c_130, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_119])).
% 2.15/1.34  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_130])).
% 2.15/1.34  tff(c_137, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_114])).
% 2.15/1.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.34  tff(c_139, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_137, c_2])).
% 2.15/1.34  tff(c_142, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_16, c_139])).
% 2.15/1.34  tff(c_10, plain, (![A_3, B_4, C_8]: (r2_hidden('#skF_1'(A_3, B_4, C_8), B_4) | r1_tarski(B_4, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.34  tff(c_43, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_26, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_36])).
% 2.15/1.34  tff(c_22, plain, (![D_17]: (r2_hidden(D_17, '#skF_3') | ~r2_hidden(D_17, '#skF_4') | ~m1_subset_1(D_17, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.34  tff(c_54, plain, (![A_26]: (r2_hidden(A_26, '#skF_3') | ~r2_hidden(A_26, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_22])).
% 2.15/1.34  tff(c_148, plain, (![B_46, A_47]: (r1_tarski(B_46, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_47)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~r2_hidden('#skF_1'(A_47, B_46, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_101])).
% 2.15/1.34  tff(c_156, plain, (![A_3]: (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_10, c_148])).
% 2.15/1.34  tff(c_162, plain, (![A_48]: (~m1_subset_1('#skF_3', k1_zfmisc_1(A_48)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_48)))), inference(negUnitSimplification, [status(thm)], [c_142, c_142, c_156])).
% 2.15/1.34  tff(c_173, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_162])).
% 2.15/1.34  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_173])).
% 2.15/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.34  
% 2.15/1.34  Inference rules
% 2.15/1.34  ----------------------
% 2.15/1.34  #Ref     : 0
% 2.15/1.34  #Sup     : 30
% 2.15/1.34  #Fact    : 0
% 2.15/1.34  #Define  : 0
% 2.15/1.34  #Split   : 2
% 2.15/1.34  #Chain   : 0
% 2.15/1.34  #Close   : 0
% 2.15/1.34  
% 2.15/1.34  Ordering : KBO
% 2.15/1.34  
% 2.15/1.34  Simplification rules
% 2.15/1.34  ----------------------
% 2.15/1.34  #Subsume      : 7
% 2.15/1.34  #Demod        : 6
% 2.15/1.34  #Tautology    : 6
% 2.15/1.34  #SimpNegUnit  : 2
% 2.15/1.34  #BackRed      : 0
% 2.15/1.34  
% 2.15/1.34  #Partial instantiations: 0
% 2.15/1.34  #Strategies tried      : 1
% 2.15/1.34  
% 2.15/1.34  Timing (in seconds)
% 2.15/1.34  ----------------------
% 2.15/1.34  Preprocessing        : 0.30
% 2.15/1.34  Parsing              : 0.17
% 2.15/1.34  CNF conversion       : 0.02
% 2.15/1.34  Main loop            : 0.17
% 2.15/1.34  Inferencing          : 0.06
% 2.15/1.34  Reduction            : 0.04
% 2.15/1.34  Demodulation         : 0.03
% 2.15/1.34  BG Simplification    : 0.01
% 2.15/1.34  Subsumption          : 0.04
% 2.15/1.34  Abstraction          : 0.01
% 2.15/1.34  MUC search           : 0.00
% 2.15/1.34  Cooper               : 0.00
% 2.15/1.34  Total                : 0.50
% 2.15/1.34  Index Insertion      : 0.00
% 2.15/1.34  Index Deletion       : 0.00
% 2.15/1.34  Index Matching       : 0.00
% 2.15/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
