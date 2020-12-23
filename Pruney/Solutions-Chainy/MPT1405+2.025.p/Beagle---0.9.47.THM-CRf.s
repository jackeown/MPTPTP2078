%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 163 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_20,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_47])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_22])).

tff(c_57,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_57])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_tops_1(A_7,k2_struct_0(A_7)) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [C_27,A_28,B_29] :
      ( m2_connsp_2(C_27,A_28,B_29)
      | ~ r1_tarski(B_29,k1_tops_1(A_28,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_304,plain,(
    ! [A_65,B_66] :
      ( m2_connsp_2(k2_struct_0(A_65),A_65,B_66)
      | ~ r1_tarski(B_66,k2_struct_0(A_65))
      | ~ m1_subset_1(k2_struct_0(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_306,plain,(
    ! [B_66] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_66)
      | ~ r1_tarski(B_66,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_304])).

tff(c_313,plain,(
    ! [B_67] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_67)
      | ~ r1_tarski(B_67,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_26,c_24,c_51,c_29,c_306])).

tff(c_316,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_313])).

tff(c_327,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_316])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.29  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.13/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.13/1.29  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.13/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.29  
% 2.13/1.30  tff(f_74, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.13/1.30  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.13/1.30  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.13/1.30  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.13/1.30  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.13/1.30  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.13/1.30  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.13/1.30  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.13/1.30  tff(c_20, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.30  tff(c_41, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.30  tff(c_47, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_12, c_41])).
% 2.13/1.30  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_47])).
% 2.13/1.30  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_22])).
% 2.13/1.30  tff(c_57, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_67, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_57])).
% 2.13/1.30  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.30  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.30  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.30  tff(c_29, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.13/1.30  tff(c_14, plain, (![A_7]: (k1_tops_1(A_7, k2_struct_0(A_7))=k2_struct_0(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.30  tff(c_80, plain, (![C_27, A_28, B_29]: (m2_connsp_2(C_27, A_28, B_29) | ~r1_tarski(B_29, k1_tops_1(A_28, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.30  tff(c_304, plain, (![A_65, B_66]: (m2_connsp_2(k2_struct_0(A_65), A_65, B_66) | ~r1_tarski(B_66, k2_struct_0(A_65)) | ~m1_subset_1(k2_struct_0(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(superposition, [status(thm), theory('equality')], [c_14, c_80])).
% 2.13/1.30  tff(c_306, plain, (![B_66]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_66) | ~r1_tarski(B_66, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_304])).
% 2.13/1.30  tff(c_313, plain, (![B_67]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_67) | ~r1_tarski(B_67, k2_struct_0('#skF_1')) | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_26, c_24, c_51, c_29, c_306])).
% 2.13/1.30  tff(c_316, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_313])).
% 2.13/1.30  tff(c_327, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_316])).
% 2.13/1.30  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_327])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 64
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 2
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 10
% 2.13/1.30  #Demod        : 88
% 2.13/1.30  #Tautology    : 18
% 2.13/1.30  #SimpNegUnit  : 1
% 2.13/1.30  #BackRed      : 1
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.31  Preprocessing        : 0.27
% 2.13/1.31  Parsing              : 0.14
% 2.13/1.31  CNF conversion       : 0.02
% 2.13/1.31  Main loop            : 0.26
% 2.13/1.31  Inferencing          : 0.10
% 2.13/1.31  Reduction            : 0.08
% 2.13/1.31  Demodulation         : 0.05
% 2.13/1.31  BG Simplification    : 0.01
% 2.13/1.31  Subsumption          : 0.06
% 2.13/1.31  Abstraction          : 0.01
% 2.13/1.31  MUC search           : 0.00
% 2.13/1.31  Cooper               : 0.00
% 2.13/1.31  Total                : 0.56
% 2.13/1.31  Index Insertion      : 0.00
% 2.13/1.31  Index Deletion       : 0.00
% 2.13/1.31  Index Matching       : 0.00
% 2.13/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
