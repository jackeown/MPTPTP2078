%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:51 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 123 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_6,B_7,C_11] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_11),B_7)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_6,B_7,C_11] :
      ( m1_subset_1('#skF_2'(A_6,B_7,C_11),A_6)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    r1_tarski(k7_setfam_1('#skF_3','#skF_4'),k7_setfam_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_78,plain,(
    ! [A_45,C_46,B_47] :
      ( r2_hidden(k3_subset_1(A_45,C_46),k7_setfam_1(A_45,B_47))
      | ~ r2_hidden(C_46,B_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_67,C_68,B_69,B_70] :
      ( r2_hidden(k3_subset_1(A_67,C_68),B_69)
      | ~ r1_tarski(k7_setfam_1(A_67,B_70),B_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_143,plain,(
    ! [C_68] :
      ( r2_hidden(k3_subset_1('#skF_3',C_68),k7_setfam_1('#skF_3','#skF_5'))
      | ~ r2_hidden(C_68,'#skF_4')
      | ~ m1_subset_1(C_68,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_149,plain,(
    ! [C_71] :
      ( r2_hidden(k3_subset_1('#skF_3',C_71),k7_setfam_1('#skF_3','#skF_5'))
      | ~ r2_hidden(C_71,'#skF_4')
      | ~ m1_subset_1(C_71,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_143])).

tff(c_16,plain,(
    ! [C_16,B_14,A_13] :
      ( r2_hidden(C_16,B_14)
      | ~ r2_hidden(k3_subset_1(A_13,C_16),k7_setfam_1(A_13,B_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [C_71] :
      ( r2_hidden(C_71,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ r2_hidden(C_71,'#skF_4')
      | ~ m1_subset_1(C_71,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_149,c_16])).

tff(c_159,plain,(
    ! [C_72] :
      ( r2_hidden(C_72,'#skF_5')
      | ~ r2_hidden(C_72,'#skF_4')
      | ~ m1_subset_1(C_72,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_152])).

tff(c_247,plain,(
    ! [B_91,C_92] :
      ( r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'),B_91,C_92),'#skF_5')
      | ~ r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'),B_91,C_92),'#skF_4')
      | r1_tarski(B_91,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_8,plain,(
    ! [A_6,B_7,C_11] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_11),C_11)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_253,plain,(
    ! [B_91] :
      ( ~ r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'),B_91,'#skF_5'),'#skF_4')
      | r1_tarski(B_91,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_261,plain,(
    ! [B_93] :
      ( ~ r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'),B_93,'#skF_5'),'#skF_4')
      | r1_tarski(B_93,'#skF_5')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_253])).

tff(c_269,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_261])).

tff(c_275,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_269])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:47:09 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.35  
% 2.33/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.33/1.35  
% 2.33/1.35  %Foreground sorts:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Background operators:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Foreground operators:
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.35  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.33/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.33/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.33/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.33/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.35  
% 2.33/1.37  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 2.33/1.37  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.33/1.37  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 2.33/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.33/1.37  tff(c_18, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.37  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.37  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.37  tff(c_10, plain, (![A_6, B_7, C_11]: (r2_hidden('#skF_2'(A_6, B_7, C_11), B_7) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.37  tff(c_12, plain, (![A_6, B_7, C_11]: (m1_subset_1('#skF_2'(A_6, B_7, C_11), A_6) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.37  tff(c_20, plain, (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), k7_setfam_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.37  tff(c_78, plain, (![A_45, C_46, B_47]: (r2_hidden(k3_subset_1(A_45, C_46), k7_setfam_1(A_45, B_47)) | ~r2_hidden(C_46, B_47) | ~m1_subset_1(C_46, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.37  tff(c_135, plain, (![A_67, C_68, B_69, B_70]: (r2_hidden(k3_subset_1(A_67, C_68), B_69) | ~r1_tarski(k7_setfam_1(A_67, B_70), B_69) | ~r2_hidden(C_68, B_70) | ~m1_subset_1(C_68, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.33/1.37  tff(c_143, plain, (![C_68]: (r2_hidden(k3_subset_1('#skF_3', C_68), k7_setfam_1('#skF_3', '#skF_5')) | ~r2_hidden(C_68, '#skF_4') | ~m1_subset_1(C_68, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_20, c_135])).
% 2.33/1.37  tff(c_149, plain, (![C_71]: (r2_hidden(k3_subset_1('#skF_3', C_71), k7_setfam_1('#skF_3', '#skF_5')) | ~r2_hidden(C_71, '#skF_4') | ~m1_subset_1(C_71, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_143])).
% 2.33/1.37  tff(c_16, plain, (![C_16, B_14, A_13]: (r2_hidden(C_16, B_14) | ~r2_hidden(k3_subset_1(A_13, C_16), k7_setfam_1(A_13, B_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.37  tff(c_152, plain, (![C_71]: (r2_hidden(C_71, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~r2_hidden(C_71, '#skF_4') | ~m1_subset_1(C_71, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_149, c_16])).
% 2.33/1.37  tff(c_159, plain, (![C_72]: (r2_hidden(C_72, '#skF_5') | ~r2_hidden(C_72, '#skF_4') | ~m1_subset_1(C_72, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_152])).
% 2.33/1.37  tff(c_247, plain, (![B_91, C_92]: (r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'), B_91, C_92), '#skF_5') | ~r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'), B_91, C_92), '#skF_4') | r1_tarski(B_91, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_12, c_159])).
% 2.33/1.37  tff(c_8, plain, (![A_6, B_7, C_11]: (~r2_hidden('#skF_2'(A_6, B_7, C_11), C_11) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.37  tff(c_253, plain, (![B_91]: (~r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'), B_91, '#skF_5'), '#skF_4') | r1_tarski(B_91, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_247, c_8])).
% 2.33/1.37  tff(c_261, plain, (![B_93]: (~r2_hidden('#skF_2'(k1_zfmisc_1('#skF_3'), B_93, '#skF_5'), '#skF_4') | r1_tarski(B_93, '#skF_5') | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_253])).
% 2.33/1.37  tff(c_269, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_261])).
% 2.33/1.37  tff(c_275, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_269])).
% 2.33/1.37  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_275])).
% 2.33/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.37  
% 2.33/1.37  Inference rules
% 2.33/1.37  ----------------------
% 2.33/1.37  #Ref     : 0
% 2.33/1.37  #Sup     : 58
% 2.33/1.37  #Fact    : 0
% 2.33/1.37  #Define  : 0
% 2.33/1.37  #Split   : 1
% 2.33/1.37  #Chain   : 0
% 2.33/1.37  #Close   : 0
% 2.33/1.37  
% 2.33/1.37  Ordering : KBO
% 2.33/1.37  
% 2.33/1.37  Simplification rules
% 2.33/1.37  ----------------------
% 2.33/1.37  #Subsume      : 16
% 2.33/1.37  #Demod        : 9
% 2.33/1.37  #Tautology    : 4
% 2.33/1.37  #SimpNegUnit  : 1
% 2.33/1.37  #BackRed      : 0
% 2.33/1.37  
% 2.33/1.37  #Partial instantiations: 0
% 2.33/1.37  #Strategies tried      : 1
% 2.33/1.37  
% 2.33/1.37  Timing (in seconds)
% 2.33/1.37  ----------------------
% 2.33/1.37  Preprocessing        : 0.29
% 2.33/1.37  Parsing              : 0.16
% 2.33/1.37  CNF conversion       : 0.02
% 2.33/1.37  Main loop            : 0.26
% 2.33/1.37  Inferencing          : 0.10
% 2.33/1.37  Reduction            : 0.06
% 2.33/1.37  Demodulation         : 0.04
% 2.33/1.37  BG Simplification    : 0.01
% 2.33/1.37  Subsumption          : 0.07
% 2.33/1.37  Abstraction          : 0.01
% 2.33/1.37  MUC search           : 0.00
% 2.33/1.37  Cooper               : 0.00
% 2.33/1.37  Total                : 0.58
% 2.33/1.37  Index Insertion      : 0.00
% 2.33/1.37  Index Deletion       : 0.00
% 2.33/1.37  Index Matching       : 0.00
% 2.33/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
