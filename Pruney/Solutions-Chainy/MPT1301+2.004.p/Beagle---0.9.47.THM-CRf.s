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
% DateTime   : Thu Dec  3 10:22:45 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 177 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v2_tops_2(C,A) )
                 => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_20,plain,(
    ~ v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_1'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_146,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),B_58)
      | v2_tops_2(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57))))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_156,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_150])).

tff(c_157,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_156])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(k1_tarski(A_36),B_37) = B_37
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(k1_tarski(A_45),C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_98,plain,(
    ! [A_48] :
      ( r1_tarski(k1_tarski(A_48),'#skF_4')
      | ~ r2_hidden(A_48,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,'#skF_4')
      | ~ r2_hidden(A_48,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_98,c_6])).

tff(c_167,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_108])).

tff(c_254,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_pre_topc(C_72,A_73)
      | ~ r2_hidden(C_72,B_74)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v2_tops_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73))))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_352,plain,(
    ! [A_94] :
      ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),A_94)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v2_tops_2('#skF_4',A_94)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94))))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_167,c_254])).

tff(c_356,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v2_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_352])).

tff(c_367,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_22,c_356])).

tff(c_368,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_367])).

tff(c_14,plain,(
    ! [A_11,B_17] :
      ( ~ v4_pre_topc('#skF_1'(A_11,B_17),A_11)
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_376,plain,
    ( v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_368,c_14])).

tff(c_379,plain,(
    v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_376])).

tff(c_381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.29/1.32  
% 2.29/1.32  %Foreground sorts:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Background operators:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Foreground operators:
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.32  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.29/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.32  
% 2.61/1.33  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 2.61/1.33  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 2.61/1.33  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.61/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.61/1.33  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.61/1.33  tff(c_20, plain, (~v2_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.33  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.33  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.33  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.33  tff(c_22, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.33  tff(c_18, plain, (![A_11, B_17]: (m1_subset_1('#skF_1'(A_11, B_17), k1_zfmisc_1(u1_struct_0(A_11))) | v2_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.33  tff(c_146, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), B_58) | v2_tops_2(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57)))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.33  tff(c_150, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_146])).
% 2.61/1.33  tff(c_156, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_150])).
% 2.61/1.33  tff(c_157, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_156])).
% 2.61/1.33  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.33  tff(c_41, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.33  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.33  tff(c_60, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)=B_37 | ~r2_hidden(A_36, B_37))), inference(resolution, [status(thm)], [c_41, c_4])).
% 2.61/1.33  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.33  tff(c_88, plain, (![A_45, C_46, B_47]: (r1_tarski(k1_tarski(A_45), C_46) | ~r1_tarski(B_47, C_46) | ~r2_hidden(A_45, B_47))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2])).
% 2.61/1.33  tff(c_98, plain, (![A_48]: (r1_tarski(k1_tarski(A_48), '#skF_4') | ~r2_hidden(A_48, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_88])).
% 2.61/1.33  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.33  tff(c_108, plain, (![A_48]: (r2_hidden(A_48, '#skF_4') | ~r2_hidden(A_48, '#skF_3'))), inference(resolution, [status(thm)], [c_98, c_6])).
% 2.61/1.33  tff(c_167, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_157, c_108])).
% 2.61/1.33  tff(c_254, plain, (![C_72, A_73, B_74]: (v4_pre_topc(C_72, A_73) | ~r2_hidden(C_72, B_74) | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~v2_tops_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73)))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.33  tff(c_352, plain, (![A_94]: (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_94) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_94))) | ~v2_tops_2('#skF_4', A_94) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94)))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_167, c_254])).
% 2.61/1.33  tff(c_356, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v2_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_352])).
% 2.61/1.33  tff(c_367, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_22, c_356])).
% 2.61/1.33  tff(c_368, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_367])).
% 2.61/1.33  tff(c_14, plain, (![A_11, B_17]: (~v4_pre_topc('#skF_1'(A_11, B_17), A_11) | v2_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.33  tff(c_376, plain, (v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_368, c_14])).
% 2.61/1.33  tff(c_379, plain, (v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_376])).
% 2.61/1.33  tff(c_381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_379])).
% 2.61/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  Inference rules
% 2.61/1.33  ----------------------
% 2.61/1.33  #Ref     : 0
% 2.61/1.33  #Sup     : 76
% 2.61/1.33  #Fact    : 0
% 2.61/1.33  #Define  : 0
% 2.61/1.33  #Split   : 8
% 2.61/1.33  #Chain   : 0
% 2.61/1.33  #Close   : 0
% 2.61/1.33  
% 2.61/1.33  Ordering : KBO
% 2.61/1.33  
% 2.61/1.33  Simplification rules
% 2.61/1.33  ----------------------
% 2.61/1.33  #Subsume      : 16
% 2.61/1.33  #Demod        : 29
% 2.61/1.33  #Tautology    : 18
% 2.61/1.33  #SimpNegUnit  : 5
% 2.61/1.33  #BackRed      : 0
% 2.61/1.33  
% 2.61/1.33  #Partial instantiations: 0
% 2.61/1.33  #Strategies tried      : 1
% 2.61/1.33  
% 2.61/1.33  Timing (in seconds)
% 2.61/1.33  ----------------------
% 2.61/1.33  Preprocessing        : 0.27
% 2.61/1.33  Parsing              : 0.15
% 2.61/1.33  CNF conversion       : 0.02
% 2.61/1.33  Main loop            : 0.30
% 2.61/1.33  Inferencing          : 0.11
% 2.61/1.33  Reduction            : 0.08
% 2.61/1.33  Demodulation         : 0.05
% 2.61/1.33  BG Simplification    : 0.01
% 2.61/1.33  Subsumption          : 0.08
% 2.61/1.33  Abstraction          : 0.01
% 2.61/1.33  MUC search           : 0.00
% 2.61/1.33  Cooper               : 0.00
% 2.61/1.33  Total                : 0.60
% 2.61/1.33  Index Insertion      : 0.00
% 2.61/1.33  Index Deletion       : 0.00
% 2.61/1.33  Index Matching       : 0.00
% 2.61/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
