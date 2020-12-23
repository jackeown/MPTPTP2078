%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   48 (  77 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 196 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    m2_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_70,plain,(
    ! [C_43,A_44,B_45] :
      ( m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m2_connsp_2(C_43,A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_75,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_72])).

tff(c_135,plain,(
    ! [B_60,A_61,C_62] :
      ( r1_tarski(B_60,k1_tops_1(A_61,C_62))
      | ~ m2_connsp_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [B_60] :
      ( r1_tarski(B_60,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_75,c_135])).

tff(c_157,plain,(
    ! [B_64] :
      ( r1_tarski(B_64,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_137])).

tff(c_163,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m2_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_167,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_163])).

tff(c_8,plain,(
    ! [A_6,B_8] :
      ( r1_tarski(k1_tops_1(A_6,B_8),B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_8])).

tff(c_80,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [C_29,B_30,A_31] :
      ( r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_34)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_32,B_33,B_2,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_2)
      | ~ r1_tarski(B_34,B_2)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_105,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),'#skF_4')
      | ~ r1_tarski(A_52,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_80,c_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_52] :
      ( ~ r1_tarski(A_52,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_52,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_170,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_113])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.16/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.16/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.30  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.16/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.30  
% 2.16/1.31  tff(f_80, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_connsp_2)).
% 2.16/1.31  tff(f_64, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 2.16/1.31  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.16/1.31  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.16/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.31  tff(c_16, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.31  tff(c_18, plain, (m2_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.31  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.31  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.31  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.31  tff(c_70, plain, (![C_43, A_44, B_45]: (m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~m2_connsp_2(C_43, A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.31  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_70])).
% 2.16/1.31  tff(c_75, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_72])).
% 2.16/1.31  tff(c_135, plain, (![B_60, A_61, C_62]: (r1_tarski(B_60, k1_tops_1(A_61, C_62)) | ~m2_connsp_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.31  tff(c_137, plain, (![B_60]: (r1_tarski(B_60, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_75, c_135])).
% 2.16/1.31  tff(c_157, plain, (![B_64]: (r1_tarski(B_64, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_137])).
% 2.16/1.31  tff(c_163, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_157])).
% 2.16/1.31  tff(c_167, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_163])).
% 2.16/1.31  tff(c_8, plain, (![A_6, B_8]: (r1_tarski(k1_tops_1(A_6, B_8), B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.31  tff(c_77, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_75, c_8])).
% 2.16/1.31  tff(c_80, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_77])).
% 2.16/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.31  tff(c_35, plain, (![C_29, B_30, A_31]: (r2_hidden(C_29, B_30) | ~r2_hidden(C_29, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.31  tff(c_39, plain, (![A_32, B_33, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_34) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_6, c_35])).
% 2.16/1.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.31  tff(c_46, plain, (![A_32, B_33, B_2, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_2) | ~r1_tarski(B_34, B_2) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_39, c_2])).
% 2.16/1.31  tff(c_105, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), '#skF_4') | ~r1_tarski(A_52, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_80, c_46])).
% 2.16/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.31  tff(c_113, plain, (![A_52]: (~r1_tarski(A_52, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_52, '#skF_4'))), inference(resolution, [status(thm)], [c_105, c_4])).
% 2.16/1.31  tff(c_170, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_167, c_113])).
% 2.16/1.31  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_170])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 31
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 2
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 3
% 2.16/1.31  #Demod        : 12
% 2.16/1.31  #Tautology    : 3
% 2.16/1.31  #SimpNegUnit  : 1
% 2.16/1.31  #BackRed      : 0
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.31  Preprocessing        : 0.30
% 2.16/1.31  Parsing              : 0.17
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.21
% 2.16/1.31  Inferencing          : 0.08
% 2.16/1.31  Reduction            : 0.05
% 2.16/1.31  Demodulation         : 0.04
% 2.16/1.31  BG Simplification    : 0.01
% 2.16/1.31  Subsumption          : 0.05
% 2.16/1.31  Abstraction          : 0.01
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.54
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.32  Index Deletion       : 0.00
% 2.16/1.32  Index Matching       : 0.00
% 2.16/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
