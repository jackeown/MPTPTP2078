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
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  80 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 233 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( v3_pre_topc(B,A)
                    & r2_hidden(C,B) )
                 => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(c_16,plain,(
    ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tops_1(A_27,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_45,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_49,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_20,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_29,A_30,C_31] :
      ( r1_tarski(B_29,k1_tops_1(A_30,C_31))
      | ~ r1_tarski(B_29,C_31)
      | ~ v3_pre_topc(B_29,A_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [B_29] :
      ( r1_tarski(B_29,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_29,'#skF_2')
      | ~ v3_pre_topc(B_29,'#skF_1')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_64,plain,(
    ! [B_36] :
      ( r1_tarski(B_36,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_36,'#skF_2')
      | ~ v3_pre_topc(B_36,'#skF_1')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_52])).

tff(c_67,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_70,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_67])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_70])).

tff(c_73,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_88,plain,(
    ! [C_40,A_41,B_42] :
      ( m1_connsp_2(C_40,A_41,B_42)
      | ~ r2_hidden(B_42,k1_tops_1(A_41,C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [B_42] :
      ( m1_connsp_2('#skF_2','#skF_1',B_42)
      | ~ r2_hidden(B_42,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_88])).

tff(c_92,plain,(
    ! [B_42] :
      ( m1_connsp_2('#skF_2','#skF_1',B_42)
      | ~ r2_hidden(B_42,'#skF_2')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_90])).

tff(c_94,plain,(
    ! [B_43] :
      ( m1_connsp_2('#skF_2','#skF_1',B_43)
      | ~ r2_hidden(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_92])).

tff(c_97,plain,
    ( m1_connsp_2('#skF_2','#skF_1','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_94])).

tff(c_100,plain,(
    m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.21  
% 2.22/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.21  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.21  
% 2.22/1.21  %Foreground sorts:
% 2.22/1.21  
% 2.22/1.21  
% 2.22/1.21  %Background operators:
% 2.22/1.21  
% 2.22/1.21  
% 2.22/1.21  %Foreground operators:
% 2.22/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.21  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.22/1.21  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.21  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.22/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.22/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.21  
% 2.22/1.22  tff(f_89, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.22/1.22  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.22/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.22  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.22/1.22  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.22/1.22  tff(c_16, plain, (~m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_22, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_40, plain, (![A_27, B_28]: (r1_tarski(k1_tops_1(A_27, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.22  tff(c_42, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.22/1.22  tff(c_45, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_42])).
% 2.22/1.22  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.22  tff(c_48, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.22/1.22  tff(c_49, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.22/1.22  tff(c_20, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.22  tff(c_50, plain, (![B_29, A_30, C_31]: (r1_tarski(B_29, k1_tops_1(A_30, C_31)) | ~r1_tarski(B_29, C_31) | ~v3_pre_topc(B_29, A_30) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.22  tff(c_52, plain, (![B_29]: (r1_tarski(B_29, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_29, '#skF_2') | ~v3_pre_topc(B_29, '#skF_1') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.22/1.22  tff(c_64, plain, (![B_36]: (r1_tarski(B_36, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_36, '#skF_2') | ~v3_pre_topc(B_36, '#skF_1') | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_52])).
% 2.22/1.22  tff(c_67, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_64])).
% 2.22/1.22  tff(c_70, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_67])).
% 2.22/1.22  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_70])).
% 2.22/1.22  tff(c_73, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 2.22/1.22  tff(c_88, plain, (![C_40, A_41, B_42]: (m1_connsp_2(C_40, A_41, B_42) | ~r2_hidden(B_42, k1_tops_1(A_41, C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.22/1.22  tff(c_90, plain, (![B_42]: (m1_connsp_2('#skF_2', '#skF_1', B_42) | ~r2_hidden(B_42, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_42, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_88])).
% 2.22/1.22  tff(c_92, plain, (![B_42]: (m1_connsp_2('#skF_2', '#skF_1', B_42) | ~r2_hidden(B_42, '#skF_2') | ~m1_subset_1(B_42, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_90])).
% 2.22/1.22  tff(c_94, plain, (![B_43]: (m1_connsp_2('#skF_2', '#skF_1', B_43) | ~r2_hidden(B_43, '#skF_2') | ~m1_subset_1(B_43, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_92])).
% 2.22/1.22  tff(c_97, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3') | ~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_94])).
% 2.22/1.22  tff(c_100, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_97])).
% 2.22/1.22  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_100])).
% 2.22/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.22  
% 2.22/1.22  Inference rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Ref     : 0
% 2.22/1.22  #Sup     : 11
% 2.22/1.22  #Fact    : 0
% 2.22/1.22  #Define  : 0
% 2.22/1.22  #Split   : 1
% 2.22/1.22  #Chain   : 0
% 2.22/1.22  #Close   : 0
% 2.22/1.22  
% 2.22/1.22  Ordering : KBO
% 2.22/1.22  
% 2.22/1.22  Simplification rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Subsume      : 0
% 2.22/1.22  #Demod        : 18
% 2.22/1.22  #Tautology    : 7
% 2.22/1.22  #SimpNegUnit  : 4
% 2.22/1.22  #BackRed      : 1
% 2.22/1.22  
% 2.22/1.22  #Partial instantiations: 0
% 2.22/1.22  #Strategies tried      : 1
% 2.22/1.22  
% 2.22/1.22  Timing (in seconds)
% 2.22/1.22  ----------------------
% 2.22/1.23  Preprocessing        : 0.30
% 2.22/1.23  Parsing              : 0.17
% 2.22/1.23  CNF conversion       : 0.02
% 2.22/1.23  Main loop            : 0.16
% 2.22/1.23  Inferencing          : 0.06
% 2.22/1.23  Reduction            : 0.05
% 2.22/1.23  Demodulation         : 0.03
% 2.22/1.23  BG Simplification    : 0.01
% 2.22/1.23  Subsumption          : 0.03
% 2.22/1.23  Abstraction          : 0.01
% 2.22/1.23  MUC search           : 0.00
% 2.22/1.23  Cooper               : 0.00
% 2.22/1.23  Total                : 0.49
% 2.22/1.23  Index Insertion      : 0.00
% 2.22/1.23  Index Deletion       : 0.00
% 2.22/1.23  Index Matching       : 0.00
% 2.22/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
