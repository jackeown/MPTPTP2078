%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 120 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_141,plain,(
    ! [A_55,B_56] :
      ( k5_setfam_1(A_55,B_56) = k3_tarski(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_145,plain,(
    k5_setfam_1('#skF_2','#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_26,plain,
    ( k5_setfam_1('#skF_2','#skF_3') != '#skF_2'
    | ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_35,plain,(
    ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( m1_setfam_1('#skF_3','#skF_2')
    | k5_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    k5_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_32])).

tff(c_79,plain,(
    ! [A_36,B_37] :
      ( k5_setfam_1(A_36,B_37) = k3_tarski(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    k5_setfam_1('#skF_2','#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_84,plain,(
    k3_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_41,plain,(
    ! [B_19,A_20] :
      ( m1_setfam_1(B_19,A_20)
      | ~ r1_tarski(A_20,k3_tarski(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [B_19] : m1_setfam_1(B_19,k3_tarski(B_19)) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_91,plain,(
    m1_setfam_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_46])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_91])).

tff(c_99,plain,(
    k5_setfam_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_146,plain,(
    k3_tarski('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_99])).

tff(c_100,plain,(
    m1_setfam_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_151,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k5_setfam_1(A_57,B_58),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_158,plain,
    ( m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_151])).

tff(c_161,plain,(
    m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [C_52,A_53,B_54] :
      ( r2_hidden(C_52,A_53)
      | ~ r2_hidden(C_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_188,plain,(
    ! [A_64,B_65,A_66] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_66)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(A_66))
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [A_67,A_68] :
      ( ~ m1_subset_1(A_67,k1_zfmisc_1(A_68))
      | r1_tarski(A_67,A_68) ) ),
    inference(resolution,[status(thm)],[c_188,c_4])).

tff(c_210,plain,(
    r1_tarski(k3_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_161,c_200])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k3_tarski(B_13))
      | ~ m1_setfam_1(B_13,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [B_13,A_12] :
      ( k3_tarski(B_13) = A_12
      | ~ r1_tarski(k3_tarski(B_13),A_12)
      | ~ m1_setfam_1(B_13,A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_220,plain,
    ( k3_tarski('#skF_3') = '#skF_2'
    | ~ m1_setfam_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_128])).

tff(c_225,plain,(
    k3_tarski('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_220])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:23:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.19  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.84/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.19  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.19  
% 1.93/1.20  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.93/1.20  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.93/1.20  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.20  tff(f_49, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.93/1.20  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 1.93/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.20  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.93/1.20  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.20  tff(c_141, plain, (![A_55, B_56]: (k5_setfam_1(A_55, B_56)=k3_tarski(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.20  tff(c_145, plain, (k5_setfam_1('#skF_2', '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_141])).
% 1.93/1.20  tff(c_26, plain, (k5_setfam_1('#skF_2', '#skF_3')!='#skF_2' | ~m1_setfam_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.20  tff(c_35, plain, (~m1_setfam_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 1.93/1.20  tff(c_32, plain, (m1_setfam_1('#skF_3', '#skF_2') | k5_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.20  tff(c_36, plain, (k5_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_35, c_32])).
% 1.93/1.20  tff(c_79, plain, (![A_36, B_37]: (k5_setfam_1(A_36, B_37)=k3_tarski(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.20  tff(c_82, plain, (k5_setfam_1('#skF_2', '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_79])).
% 1.93/1.20  tff(c_84, plain, (k3_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82])).
% 1.93/1.20  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.20  tff(c_41, plain, (![B_19, A_20]: (m1_setfam_1(B_19, A_20) | ~r1_tarski(A_20, k3_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.20  tff(c_46, plain, (![B_19]: (m1_setfam_1(B_19, k3_tarski(B_19)))), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.93/1.20  tff(c_91, plain, (m1_setfam_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_46])).
% 1.93/1.20  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_91])).
% 1.93/1.20  tff(c_99, plain, (k5_setfam_1('#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 1.93/1.20  tff(c_146, plain, (k3_tarski('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_99])).
% 1.93/1.20  tff(c_100, plain, (m1_setfam_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 1.93/1.20  tff(c_151, plain, (![A_57, B_58]: (m1_subset_1(k5_setfam_1(A_57, B_58), k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.20  tff(c_158, plain, (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_145, c_151])).
% 1.93/1.20  tff(c_161, plain, (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_158])).
% 1.93/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.20  tff(c_137, plain, (![C_52, A_53, B_54]: (r2_hidden(C_52, A_53) | ~r2_hidden(C_52, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.20  tff(c_188, plain, (![A_64, B_65, A_66]: (r2_hidden('#skF_1'(A_64, B_65), A_66) | ~m1_subset_1(A_64, k1_zfmisc_1(A_66)) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_6, c_137])).
% 1.93/1.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.20  tff(c_200, plain, (![A_67, A_68]: (~m1_subset_1(A_67, k1_zfmisc_1(A_68)) | r1_tarski(A_67, A_68))), inference(resolution, [status(thm)], [c_188, c_4])).
% 1.93/1.20  tff(c_210, plain, (r1_tarski(k3_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_161, c_200])).
% 1.93/1.20  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k3_tarski(B_13)) | ~m1_setfam_1(B_13, A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.20  tff(c_123, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.20  tff(c_128, plain, (![B_13, A_12]: (k3_tarski(B_13)=A_12 | ~r1_tarski(k3_tarski(B_13), A_12) | ~m1_setfam_1(B_13, A_12))), inference(resolution, [status(thm)], [c_16, c_123])).
% 1.93/1.20  tff(c_220, plain, (k3_tarski('#skF_3')='#skF_2' | ~m1_setfam_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_210, c_128])).
% 1.93/1.20  tff(c_225, plain, (k3_tarski('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_220])).
% 1.93/1.20  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_225])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 41
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 1
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 0
% 1.93/1.20  #Demod        : 11
% 1.93/1.20  #Tautology    : 17
% 1.93/1.20  #SimpNegUnit  : 4
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.28
% 1.93/1.20  Parsing              : 0.14
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.17
% 1.93/1.21  Inferencing          : 0.06
% 1.93/1.21  Reduction            : 0.05
% 1.93/1.21  Demodulation         : 0.03
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.03
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.48
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
