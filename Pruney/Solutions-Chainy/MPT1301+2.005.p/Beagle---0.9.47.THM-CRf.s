%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:46 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 172 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v2_tops_2(C,A) )
                 => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    ~ v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_8,B_14] :
      ( m1_subset_1('#skF_1'(A_8,B_14),k1_zfmisc_1(u1_struct_0(A_8)))
      | v2_tops_2(B_14,A_8)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_45)
      | v2_tops_2(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_83,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_84,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_83])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_37,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(A_26,C_27)
      | ~ r1_tarski(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_29] :
      ( r1_tarski(A_29,'#skF_4')
      | ~ r1_tarski(A_29,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_50,plain,(
    ! [A_30] :
      ( r1_tarski(k1_tarski(A_30),'#skF_4')
      | ~ r2_hidden(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_30] :
      ( r2_hidden(A_30,'#skF_4')
      | ~ r2_hidden(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_8])).

tff(c_91,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_57])).

tff(c_98,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_pre_topc(C_50,A_51)
      | ~ r2_hidden(C_50,B_52)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ v2_tops_2(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51))))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,(
    ! [A_54] :
      ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),A_54)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v2_tops_2('#skF_4',A_54)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54))))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_91,c_98])).

tff(c_118,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v2_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_121,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_22,c_118])).

tff(c_122,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_121])).

tff(c_14,plain,(
    ! [A_8,B_14] :
      ( ~ v4_pre_topc('#skF_1'(A_8,B_14),A_8)
      | v2_tops_2(B_14,A_8)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,
    ( v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_14])).

tff(c_127,plain,(
    v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_124])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.17  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.64/1.17  
% 1.64/1.17  %Foreground sorts:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Background operators:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Foreground operators:
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.64/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.17  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.64/1.17  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.17  
% 1.92/1.19  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 1.92/1.19  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 1.92/1.19  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.92/1.19  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.92/1.19  tff(c_20, plain, (~v2_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.19  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.19  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.19  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.19  tff(c_22, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.19  tff(c_18, plain, (![A_8, B_14]: (m1_subset_1('#skF_1'(A_8, B_14), k1_zfmisc_1(u1_struct_0(A_8))) | v2_tops_2(B_14, A_8) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.19  tff(c_73, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), B_45) | v2_tops_2(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.19  tff(c_77, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_73])).
% 1.92/1.19  tff(c_83, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_77])).
% 1.92/1.19  tff(c_84, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_83])).
% 1.92/1.19  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.19  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.19  tff(c_37, plain, (![A_26, C_27, B_28]: (r1_tarski(A_26, C_27) | ~r1_tarski(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.19  tff(c_44, plain, (![A_29]: (r1_tarski(A_29, '#skF_4') | ~r1_tarski(A_29, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_37])).
% 1.92/1.19  tff(c_50, plain, (![A_30]: (r1_tarski(k1_tarski(A_30), '#skF_4') | ~r2_hidden(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_44])).
% 1.92/1.19  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.19  tff(c_57, plain, (![A_30]: (r2_hidden(A_30, '#skF_4') | ~r2_hidden(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_8])).
% 1.92/1.19  tff(c_91, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_84, c_57])).
% 1.92/1.19  tff(c_98, plain, (![C_50, A_51, B_52]: (v4_pre_topc(C_50, A_51) | ~r2_hidden(C_50, B_52) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~v2_tops_2(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51)))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.19  tff(c_114, plain, (![A_54]: (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_54) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_54))) | ~v2_tops_2('#skF_4', A_54) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54)))) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_91, c_98])).
% 1.92/1.19  tff(c_118, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v2_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_114])).
% 1.92/1.19  tff(c_121, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_22, c_118])).
% 1.92/1.19  tff(c_122, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_121])).
% 1.92/1.19  tff(c_14, plain, (![A_8, B_14]: (~v4_pre_topc('#skF_1'(A_8, B_14), A_8) | v2_tops_2(B_14, A_8) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.19  tff(c_124, plain, (v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_122, c_14])).
% 1.92/1.19  tff(c_127, plain, (v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_124])).
% 1.92/1.19  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_127])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 18
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 0
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 3
% 1.92/1.19  #Demod        : 11
% 1.92/1.19  #Tautology    : 2
% 1.92/1.19  #SimpNegUnit  : 4
% 1.92/1.19  #BackRed      : 0
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.27
% 1.92/1.19  Parsing              : 0.15
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.16
% 1.92/1.19  Inferencing          : 0.07
% 1.92/1.19  Reduction            : 0.04
% 1.92/1.19  Demodulation         : 0.03
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.03
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.46
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
