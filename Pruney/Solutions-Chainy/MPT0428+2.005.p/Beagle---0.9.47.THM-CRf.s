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

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   57 (  91 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 155 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,(
    ! [A_55,B_56] :
      ( k5_setfam_1(A_55,B_56) = k3_tarski(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_162,plain,(
    k5_setfam_1('#skF_4','#skF_5') = k3_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_158])).

tff(c_34,plain,
    ( k5_setfam_1('#skF_4','#skF_5') != '#skF_4'
    | ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_43,plain,(
    ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( m1_setfam_1('#skF_5','#skF_4')
    | k5_setfam_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    k5_setfam_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_40])).

tff(c_88,plain,(
    ! [A_35,B_36] :
      ( k5_setfam_1(A_35,B_36) = k3_tarski(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,(
    k5_setfam_1('#skF_4','#skF_5') = k3_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_93,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_91])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [B_22,A_23] :
      ( m1_setfam_1(B_22,A_23)
      | ~ r1_tarski(A_23,k3_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [B_22] : m1_setfam_1(B_22,k3_tarski(B_22)) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_100,plain,(
    m1_setfam_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_50])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_100])).

tff(c_108,plain,(
    k5_setfam_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_163,plain,(
    k3_tarski('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_108])).

tff(c_109,plain,(
    m1_setfam_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | r1_tarski(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [C_52,A_53,B_54] :
      ( r2_hidden(C_52,A_53)
      | ~ r2_hidden(C_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_276,plain,(
    ! [A_80,B_81,A_82] :
      ( r2_hidden('#skF_3'(A_80,B_81),A_82)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(A_82))
      | r1_tarski(k3_tarski(A_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_22,c_151])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,(
    ! [A_89,B_90,A_91] :
      ( r1_tarski('#skF_3'(A_89,B_90),A_91)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(k1_zfmisc_1(A_91)))
      | r1_tarski(k3_tarski(A_89),B_90) ) ),
    inference(resolution,[status(thm)],[c_276,c_8])).

tff(c_335,plain,(
    ! [B_92] :
      ( r1_tarski('#skF_3'('#skF_5',B_92),'#skF_4')
      | r1_tarski(k3_tarski('#skF_5'),B_92) ) ),
    inference(resolution,[status(thm)],[c_32,c_331])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,k3_tarski(B_16))
      | ~ m1_setfam_1(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_130,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [B_16,A_15] :
      ( k3_tarski(B_16) = A_15
      | ~ r1_tarski(k3_tarski(B_16),A_15)
      | ~ m1_setfam_1(B_16,A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_351,plain,(
    ! [B_93] :
      ( k3_tarski('#skF_5') = B_93
      | ~ m1_setfam_1('#skF_5',B_93)
      | r1_tarski('#skF_3'('#skF_5',B_93),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_335,c_135])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( ~ r1_tarski('#skF_3'(A_8,B_9),B_9)
      | r1_tarski(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_354,plain,
    ( r1_tarski(k3_tarski('#skF_5'),'#skF_4')
    | k3_tarski('#skF_5') = '#skF_4'
    | ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_351,c_20])).

tff(c_359,plain,
    ( r1_tarski(k3_tarski('#skF_5'),'#skF_4')
    | k3_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_354])).

tff(c_360,plain,(
    r1_tarski(k3_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_359])).

tff(c_364,plain,
    ( k3_tarski('#skF_5') = '#skF_4'
    | ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_360,c_135])).

tff(c_369,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_364])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.38  
% 2.15/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.15/1.38  
% 2.15/1.38  %Foreground sorts:
% 2.15/1.38  
% 2.15/1.38  
% 2.15/1.38  %Background operators:
% 2.15/1.38  
% 2.15/1.38  
% 2.15/1.38  %Foreground operators:
% 2.15/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.38  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.15/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.38  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.15/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.38  
% 2.46/1.40  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.46/1.40  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.46/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.46/1.40  tff(f_56, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.46/1.40  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.46/1.40  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.46/1.40  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.46/1.40  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.40  tff(c_158, plain, (![A_55, B_56]: (k5_setfam_1(A_55, B_56)=k3_tarski(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.40  tff(c_162, plain, (k5_setfam_1('#skF_4', '#skF_5')=k3_tarski('#skF_5')), inference(resolution, [status(thm)], [c_32, c_158])).
% 2.46/1.40  tff(c_34, plain, (k5_setfam_1('#skF_4', '#skF_5')!='#skF_4' | ~m1_setfam_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.40  tff(c_43, plain, (~m1_setfam_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.46/1.40  tff(c_40, plain, (m1_setfam_1('#skF_5', '#skF_4') | k5_setfam_1('#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.40  tff(c_57, plain, (k5_setfam_1('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_43, c_40])).
% 2.46/1.40  tff(c_88, plain, (![A_35, B_36]: (k5_setfam_1(A_35, B_36)=k3_tarski(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.40  tff(c_91, plain, (k5_setfam_1('#skF_4', '#skF_5')=k3_tarski('#skF_5')), inference(resolution, [status(thm)], [c_32, c_88])).
% 2.46/1.40  tff(c_93, plain, (k3_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_91])).
% 2.46/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.40  tff(c_45, plain, (![B_22, A_23]: (m1_setfam_1(B_22, A_23) | ~r1_tarski(A_23, k3_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.40  tff(c_50, plain, (![B_22]: (m1_setfam_1(B_22, k3_tarski(B_22)))), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.46/1.40  tff(c_100, plain, (m1_setfam_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_93, c_50])).
% 2.46/1.40  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_100])).
% 2.46/1.40  tff(c_108, plain, (k5_setfam_1('#skF_4', '#skF_5')!='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 2.46/1.40  tff(c_163, plain, (k3_tarski('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_108])).
% 2.46/1.40  tff(c_109, plain, (m1_setfam_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.46/1.40  tff(c_22, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), A_8) | r1_tarski(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.46/1.40  tff(c_151, plain, (![C_52, A_53, B_54]: (r2_hidden(C_52, A_53) | ~r2_hidden(C_52, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.40  tff(c_276, plain, (![A_80, B_81, A_82]: (r2_hidden('#skF_3'(A_80, B_81), A_82) | ~m1_subset_1(A_80, k1_zfmisc_1(A_82)) | r1_tarski(k3_tarski(A_80), B_81))), inference(resolution, [status(thm)], [c_22, c_151])).
% 2.46/1.40  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.40  tff(c_331, plain, (![A_89, B_90, A_91]: (r1_tarski('#skF_3'(A_89, B_90), A_91) | ~m1_subset_1(A_89, k1_zfmisc_1(k1_zfmisc_1(A_91))) | r1_tarski(k3_tarski(A_89), B_90))), inference(resolution, [status(thm)], [c_276, c_8])).
% 2.46/1.40  tff(c_335, plain, (![B_92]: (r1_tarski('#skF_3'('#skF_5', B_92), '#skF_4') | r1_tarski(k3_tarski('#skF_5'), B_92))), inference(resolution, [status(thm)], [c_32, c_331])).
% 2.46/1.40  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(A_15, k3_tarski(B_16)) | ~m1_setfam_1(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.40  tff(c_130, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.40  tff(c_135, plain, (![B_16, A_15]: (k3_tarski(B_16)=A_15 | ~r1_tarski(k3_tarski(B_16), A_15) | ~m1_setfam_1(B_16, A_15))), inference(resolution, [status(thm)], [c_26, c_130])).
% 2.46/1.40  tff(c_351, plain, (![B_93]: (k3_tarski('#skF_5')=B_93 | ~m1_setfam_1('#skF_5', B_93) | r1_tarski('#skF_3'('#skF_5', B_93), '#skF_4'))), inference(resolution, [status(thm)], [c_335, c_135])).
% 2.46/1.40  tff(c_20, plain, (![A_8, B_9]: (~r1_tarski('#skF_3'(A_8, B_9), B_9) | r1_tarski(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.46/1.40  tff(c_354, plain, (r1_tarski(k3_tarski('#skF_5'), '#skF_4') | k3_tarski('#skF_5')='#skF_4' | ~m1_setfam_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_351, c_20])).
% 2.46/1.40  tff(c_359, plain, (r1_tarski(k3_tarski('#skF_5'), '#skF_4') | k3_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_354])).
% 2.46/1.40  tff(c_360, plain, (r1_tarski(k3_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_163, c_359])).
% 2.46/1.40  tff(c_364, plain, (k3_tarski('#skF_5')='#skF_4' | ~m1_setfam_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_360, c_135])).
% 2.46/1.40  tff(c_369, plain, (k3_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_364])).
% 2.46/1.40  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_369])).
% 2.46/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.40  
% 2.46/1.40  Inference rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Ref     : 0
% 2.46/1.40  #Sup     : 68
% 2.46/1.40  #Fact    : 0
% 2.46/1.40  #Define  : 0
% 2.46/1.40  #Split   : 1
% 2.46/1.40  #Chain   : 0
% 2.46/1.40  #Close   : 0
% 2.46/1.40  
% 2.46/1.40  Ordering : KBO
% 2.46/1.40  
% 2.46/1.40  Simplification rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Subsume      : 3
% 2.46/1.40  #Demod        : 12
% 2.46/1.40  #Tautology    : 18
% 2.46/1.40  #SimpNegUnit  : 5
% 2.46/1.40  #BackRed      : 1
% 2.46/1.40  
% 2.46/1.40  #Partial instantiations: 0
% 2.46/1.40  #Strategies tried      : 1
% 2.46/1.40  
% 2.46/1.40  Timing (in seconds)
% 2.46/1.40  ----------------------
% 2.46/1.40  Preprocessing        : 0.32
% 2.46/1.40  Parsing              : 0.17
% 2.46/1.40  CNF conversion       : 0.02
% 2.46/1.40  Main loop            : 0.25
% 2.46/1.40  Inferencing          : 0.10
% 2.46/1.40  Reduction            : 0.06
% 2.46/1.40  Demodulation         : 0.04
% 2.46/1.40  BG Simplification    : 0.02
% 2.46/1.40  Subsumption          : 0.05
% 2.46/1.40  Abstraction          : 0.02
% 2.46/1.40  MUC search           : 0.00
% 2.46/1.40  Cooper               : 0.00
% 2.46/1.40  Total                : 0.60
% 2.46/1.40  Index Insertion      : 0.00
% 2.46/1.40  Index Deletion       : 0.00
% 2.46/1.40  Index Matching       : 0.00
% 2.46/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
