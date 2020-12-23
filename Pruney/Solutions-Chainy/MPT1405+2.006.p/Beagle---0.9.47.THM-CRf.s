%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 155 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 370 expanded)
%              Number of equality atoms :    7 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_63,axiom,(
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

tff(c_22,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = k2_struct_0(A_18)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_43,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_24])).

tff(c_50,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_tops_1(A_7,k2_struct_0(A_7)) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [C_27,A_28,B_29] :
      ( m2_connsp_2(C_27,A_28,B_29)
      | ~ r1_tarski(B_29,k1_tops_1(A_28,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_123,plain,(
    ! [C_37,A_38] :
      ( m2_connsp_2(C_37,A_38,k1_tops_1(A_38,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(k1_tops_1(A_38,C_37),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_130,plain,(
    ! [C_37] :
      ( m2_connsp_2(C_37,'#skF_1',k1_tops_1('#skF_1',C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1',C_37),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_123])).

tff(c_145,plain,(
    ! [C_40] :
      ( m2_connsp_2(C_40,'#skF_1',k1_tops_1('#skF_1',C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1',C_40),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_43,c_130])).

tff(c_148,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',k1_tops_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_145])).

tff(c_153,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',k1_tops_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_148])).

tff(c_155,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_164,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_170,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_282,plain,(
    ! [A_54,B_55] :
      ( m2_connsp_2(k2_struct_0(A_54),A_54,B_55)
      | ~ r1_tarski(B_55,k2_struct_0(A_54))
      | ~ m1_subset_1(k2_struct_0(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_287,plain,(
    ! [B_55] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_55)
      | ~ r1_tarski(B_55,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_282])).

tff(c_291,plain,(
    ! [B_56] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_56)
      | ~ r1_tarski(B_56,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_28,c_26,c_43,c_170,c_287])).

tff(c_301,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_291])).

tff(c_308,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_301])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:20:27 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  
% 2.22/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.22/1.41  
% 2.22/1.41  %Foreground sorts:
% 2.22/1.41  
% 2.22/1.41  
% 2.22/1.41  %Background operators:
% 2.22/1.41  
% 2.22/1.41  
% 2.22/1.41  %Foreground operators:
% 2.22/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.22/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.22/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.22/1.41  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.22/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.41  
% 2.22/1.42  tff(f_76, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.22/1.42  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.22/1.42  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.22/1.42  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.42  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.22/1.42  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.22/1.42  tff(c_22, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.42  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.42  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.42  tff(c_34, plain, (![A_18]: (u1_struct_0(A_18)=k2_struct_0(A_18) | ~l1_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.42  tff(c_39, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_14, c_34])).
% 2.22/1.42  tff(c_43, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_39])).
% 2.22/1.42  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.42  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_24])).
% 2.22/1.42  tff(c_50, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.42  tff(c_58, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_50])).
% 2.22/1.42  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.42  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.42  tff(c_16, plain, (![A_7]: (k1_tops_1(A_7, k2_struct_0(A_7))=k2_struct_0(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.22/1.42  tff(c_79, plain, (![C_27, A_28, B_29]: (m2_connsp_2(C_27, A_28, B_29) | ~r1_tarski(B_29, k1_tops_1(A_28, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.42  tff(c_123, plain, (![C_37, A_38]: (m2_connsp_2(C_37, A_38, k1_tops_1(A_38, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(k1_tops_1(A_38, C_37), k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.22/1.42  tff(c_130, plain, (![C_37]: (m2_connsp_2(C_37, '#skF_1', k1_tops_1('#skF_1', C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', C_37), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_123])).
% 2.22/1.42  tff(c_145, plain, (![C_40]: (m2_connsp_2(C_40, '#skF_1', k1_tops_1('#skF_1', C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', C_40), k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_43, c_130])).
% 2.22/1.42  tff(c_148, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', k1_tops_1('#skF_1', k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_145])).
% 2.22/1.42  tff(c_153, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', k1_tops_1('#skF_1', k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_148])).
% 2.22/1.42  tff(c_155, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_153])).
% 2.22/1.42  tff(c_164, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_155])).
% 2.22/1.42  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 2.22/1.42  tff(c_170, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_153])).
% 2.22/1.42  tff(c_282, plain, (![A_54, B_55]: (m2_connsp_2(k2_struct_0(A_54), A_54, B_55) | ~r1_tarski(B_55, k2_struct_0(A_54)) | ~m1_subset_1(k2_struct_0(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(superposition, [status(thm), theory('equality')], [c_16, c_79])).
% 2.22/1.42  tff(c_287, plain, (![B_55]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_55) | ~r1_tarski(B_55, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_282])).
% 2.22/1.42  tff(c_291, plain, (![B_56]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_56) | ~r1_tarski(B_56, k2_struct_0('#skF_1')) | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_28, c_26, c_43, c_170, c_287])).
% 2.22/1.42  tff(c_301, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_291])).
% 2.22/1.42  tff(c_308, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_301])).
% 2.22/1.42  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_308])).
% 2.22/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.42  
% 2.22/1.42  Inference rules
% 2.22/1.42  ----------------------
% 2.22/1.42  #Ref     : 0
% 2.22/1.42  #Sup     : 59
% 2.22/1.42  #Fact    : 0
% 2.22/1.42  #Define  : 0
% 2.22/1.42  #Split   : 4
% 2.22/1.42  #Chain   : 0
% 2.22/1.42  #Close   : 0
% 2.22/1.42  
% 2.22/1.42  Ordering : KBO
% 2.22/1.42  
% 2.22/1.42  Simplification rules
% 2.22/1.42  ----------------------
% 2.22/1.42  #Subsume      : 5
% 2.22/1.42  #Demod        : 64
% 2.22/1.42  #Tautology    : 18
% 2.22/1.42  #SimpNegUnit  : 1
% 2.22/1.42  #BackRed      : 1
% 2.22/1.42  
% 2.22/1.42  #Partial instantiations: 0
% 2.22/1.42  #Strategies tried      : 1
% 2.22/1.42  
% 2.22/1.42  Timing (in seconds)
% 2.22/1.42  ----------------------
% 2.22/1.43  Preprocessing        : 0.30
% 2.22/1.43  Parsing              : 0.15
% 2.22/1.43  CNF conversion       : 0.02
% 2.22/1.43  Main loop            : 0.24
% 2.22/1.43  Inferencing          : 0.08
% 2.22/1.43  Reduction            : 0.07
% 2.22/1.43  Demodulation         : 0.05
% 2.22/1.43  BG Simplification    : 0.01
% 2.22/1.43  Subsumption          : 0.05
% 2.22/1.43  Abstraction          : 0.01
% 2.22/1.43  MUC search           : 0.00
% 2.22/1.43  Cooper               : 0.00
% 2.22/1.43  Total                : 0.57
% 2.22/1.43  Index Insertion      : 0.00
% 2.22/1.43  Index Deletion       : 0.00
% 2.22/1.43  Index Matching       : 0.00
% 2.22/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
