%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:46 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
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

tff(f_70,negated_conjecture,(
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

tff(f_55,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_18,plain,(
    ~ v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_9,B_15] :
      ( m1_subset_1('#skF_1'(A_9,B_15),k1_zfmisc_1(u1_struct_0(A_9)))
      | v2_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_55)
      | v2_tops_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54))))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_98,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_99,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_98])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,'#skF_4')
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_48,plain,(
    ! [A_31] :
      ( r1_tarski(k1_tarski(A_31),'#skF_4')
      | ~ r2_hidden(A_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_31] :
      ( r2_hidden(A_31,'#skF_4')
      | ~ r2_hidden(A_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_112,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_55])).

tff(c_131,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_pre_topc(C_59,A_60)
      | ~ r2_hidden(C_59,B_61)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v2_tops_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_163,plain,(
    ! [A_67] :
      ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),A_67)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v2_tops_2('#skF_4',A_67)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_112,c_131])).

tff(c_167,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v2_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_163])).

tff(c_178,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_20,c_167])).

tff(c_179,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_178])).

tff(c_12,plain,(
    ! [A_9,B_15] :
      ( ~ v4_pre_topc('#skF_1'(A_9,B_15),A_9)
      | v2_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_187,plain,
    ( v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_12])).

tff(c_190,plain,(
    v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.33  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.33  
% 2.09/1.33  %Foreground sorts:
% 2.09/1.33  
% 2.09/1.33  
% 2.09/1.33  %Background operators:
% 2.09/1.33  
% 2.09/1.33  
% 2.09/1.33  %Foreground operators:
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.09/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.33  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.09/1.33  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.33  
% 2.09/1.34  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.09/1.34  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 2.09/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.09/1.34  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.09/1.34  tff(c_18, plain, (~v2_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.34  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.34  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.34  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.34  tff(c_20, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.34  tff(c_16, plain, (![A_9, B_15]: (m1_subset_1('#skF_1'(A_9, B_15), k1_zfmisc_1(u1_struct_0(A_9))) | v2_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.34  tff(c_88, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), B_55) | v2_tops_2(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54)))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.34  tff(c_92, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_88])).
% 2.09/1.34  tff(c_98, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_92])).
% 2.09/1.34  tff(c_99, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_18, c_98])).
% 2.09/1.34  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.34  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.34  tff(c_35, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.34  tff(c_42, plain, (![A_30]: (r1_tarski(A_30, '#skF_4') | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.09/1.34  tff(c_48, plain, (![A_31]: (r1_tarski(k1_tarski(A_31), '#skF_4') | ~r2_hidden(A_31, '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.09/1.34  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.34  tff(c_55, plain, (![A_31]: (r2_hidden(A_31, '#skF_4') | ~r2_hidden(A_31, '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_4])).
% 2.09/1.34  tff(c_112, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_99, c_55])).
% 2.09/1.34  tff(c_131, plain, (![C_59, A_60, B_61]: (v4_pre_topc(C_59, A_60) | ~r2_hidden(C_59, B_61) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~v2_tops_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.34  tff(c_163, plain, (![A_67]: (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_67) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_67))) | ~v2_tops_2('#skF_4', A_67) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67)))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_112, c_131])).
% 2.09/1.34  tff(c_167, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v2_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_163])).
% 2.09/1.34  tff(c_178, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_20, c_167])).
% 2.09/1.34  tff(c_179, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18, c_178])).
% 2.09/1.34  tff(c_12, plain, (![A_9, B_15]: (~v4_pre_topc('#skF_1'(A_9, B_15), A_9) | v2_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.34  tff(c_187, plain, (v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_179, c_12])).
% 2.09/1.34  tff(c_190, plain, (v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_187])).
% 2.09/1.34  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_190])).
% 2.09/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.34  
% 2.09/1.34  Inference rules
% 2.09/1.34  ----------------------
% 2.09/1.34  #Ref     : 0
% 2.09/1.34  #Sup     : 31
% 2.09/1.34  #Fact    : 0
% 2.09/1.34  #Define  : 0
% 2.09/1.34  #Split   : 4
% 2.09/1.34  #Chain   : 0
% 2.09/1.34  #Close   : 0
% 2.09/1.34  
% 2.09/1.34  Ordering : KBO
% 2.09/1.34  
% 2.09/1.34  Simplification rules
% 2.09/1.34  ----------------------
% 2.09/1.34  #Subsume      : 3
% 2.09/1.34  #Demod        : 25
% 2.09/1.34  #Tautology    : 2
% 2.09/1.34  #SimpNegUnit  : 4
% 2.09/1.34  #BackRed      : 0
% 2.09/1.34  
% 2.09/1.34  #Partial instantiations: 0
% 2.09/1.34  #Strategies tried      : 1
% 2.09/1.34  
% 2.09/1.34  Timing (in seconds)
% 2.09/1.34  ----------------------
% 2.09/1.34  Preprocessing        : 0.27
% 2.09/1.34  Parsing              : 0.15
% 2.09/1.34  CNF conversion       : 0.02
% 2.09/1.34  Main loop            : 0.21
% 2.09/1.34  Inferencing          : 0.08
% 2.09/1.34  Reduction            : 0.05
% 2.09/1.34  Demodulation         : 0.04
% 2.09/1.34  BG Simplification    : 0.01
% 2.09/1.34  Subsumption          : 0.05
% 2.09/1.34  Abstraction          : 0.01
% 2.09/1.34  MUC search           : 0.00
% 2.09/1.34  Cooper               : 0.00
% 2.09/1.34  Total                : 0.50
% 2.09/1.34  Index Insertion      : 0.00
% 2.09/1.34  Index Deletion       : 0.00
% 2.09/1.34  Index Matching       : 0.00
% 2.09/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
