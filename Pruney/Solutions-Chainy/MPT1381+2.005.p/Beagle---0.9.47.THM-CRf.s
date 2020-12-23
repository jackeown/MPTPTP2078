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
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   45 (  58 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 145 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( m1_connsp_2(B,A,C)
                 => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_60,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_28])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tops_1(A_28,B_29),B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_28,A_5] :
      ( r1_tarski(k1_tops_1(A_28,A_5),A_5)
      | ~ l1_pre_topc(A_28)
      | ~ r1_tarski(A_5,u1_struct_0(A_28)) ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_16,plain,(
    m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_49,plain,(
    ! [B_32,A_33,C_34] :
      ( r2_hidden(B_32,k1_tops_1(A_33,C_34))
      | ~ m1_connsp_2(C_34,A_33,B_32)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_32,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [B_32] :
      ( r2_hidden(B_32,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_32)
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_58,plain,(
    ! [B_32] :
      ( r2_hidden(B_32,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_32)
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_54])).

tff(c_61,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_38)
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_58])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(A_40))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_39)
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_76,plain,(
    ! [B_41,B_42] :
      ( r2_hidden(B_41,B_42)
      | ~ m1_connsp_2('#skF_2','#skF_1',B_41)
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_42) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_78,plain,(
    ! [B_42] :
      ( r2_hidden('#skF_3',B_42)
      | ~ m1_connsp_2('#skF_2','#skF_1','#skF_3')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_42) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_82,plain,(
    ! [B_43] :
      ( r2_hidden('#skF_3',B_43)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_86,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_92,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22,c_86])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:23:02 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.24  
% 1.83/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.24  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.24  
% 1.83/1.24  %Foreground sorts:
% 1.83/1.24  
% 1.83/1.24  
% 1.83/1.24  %Background operators:
% 1.83/1.24  
% 1.83/1.24  
% 1.83/1.24  %Foreground operators:
% 1.83/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.83/1.24  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 1.83/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.83/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.83/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.83/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.83/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.24  
% 1.83/1.26  tff(f_78, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 1.83/1.26  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.83/1.26  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.83/1.26  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 1.83/1.26  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.83/1.26  tff(c_14, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_28, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.83/1.26  tff(c_36, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_28])).
% 1.83/1.26  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.83/1.26  tff(c_38, plain, (![A_28, B_29]: (r1_tarski(k1_tops_1(A_28, B_29), B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.26  tff(c_44, plain, (![A_28, A_5]: (r1_tarski(k1_tops_1(A_28, A_5), A_5) | ~l1_pre_topc(A_28) | ~r1_tarski(A_5, u1_struct_0(A_28)))), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.83/1.26  tff(c_16, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_18, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.83/1.26  tff(c_49, plain, (![B_32, A_33, C_34]: (r2_hidden(B_32, k1_tops_1(A_33, C_34)) | ~m1_connsp_2(C_34, A_33, B_32) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_32, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.83/1.26  tff(c_54, plain, (![B_32]: (r2_hidden(B_32, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_32) | ~m1_subset_1(B_32, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_49])).
% 1.83/1.26  tff(c_58, plain, (![B_32]: (r2_hidden(B_32, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_32) | ~m1_subset_1(B_32, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_54])).
% 1.83/1.26  tff(c_61, plain, (![B_38]: (r2_hidden(B_38, k1_tops_1('#skF_1', '#skF_2')) | ~m1_connsp_2('#skF_2', '#skF_1', B_38) | ~m1_subset_1(B_38, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_26, c_58])).
% 1.83/1.26  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.26  tff(c_71, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(A_40)) | ~m1_connsp_2('#skF_2', '#skF_1', B_39) | ~m1_subset_1(B_39, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.83/1.26  tff(c_76, plain, (![B_41, B_42]: (r2_hidden(B_41, B_42) | ~m1_connsp_2('#skF_2', '#skF_1', B_41) | ~m1_subset_1(B_41, u1_struct_0('#skF_1')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_42))), inference(resolution, [status(thm)], [c_6, c_71])).
% 1.83/1.26  tff(c_78, plain, (![B_42]: (r2_hidden('#skF_3', B_42) | ~m1_connsp_2('#skF_2', '#skF_1', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_42))), inference(resolution, [status(thm)], [c_18, c_76])).
% 1.83/1.26  tff(c_82, plain, (![B_43]: (r2_hidden('#skF_3', B_43) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_43))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_78])).
% 1.83/1.26  tff(c_86, plain, (r2_hidden('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_82])).
% 1.83/1.26  tff(c_92, plain, (r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22, c_86])).
% 1.83/1.26  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_92])).
% 1.83/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.26  
% 1.83/1.26  Inference rules
% 1.83/1.26  ----------------------
% 1.83/1.26  #Ref     : 0
% 1.83/1.26  #Sup     : 12
% 1.83/1.26  #Fact    : 0
% 1.83/1.26  #Define  : 0
% 1.83/1.26  #Split   : 0
% 1.83/1.26  #Chain   : 0
% 1.83/1.26  #Close   : 0
% 1.83/1.26  
% 1.83/1.26  Ordering : KBO
% 1.83/1.26  
% 1.83/1.26  Simplification rules
% 1.83/1.26  ----------------------
% 1.83/1.26  #Subsume      : 0
% 1.83/1.26  #Demod        : 9
% 1.83/1.26  #Tautology    : 2
% 1.83/1.26  #SimpNegUnit  : 3
% 1.83/1.26  #BackRed      : 0
% 1.83/1.26  
% 1.83/1.26  #Partial instantiations: 0
% 1.83/1.26  #Strategies tried      : 1
% 1.83/1.26  
% 1.83/1.26  Timing (in seconds)
% 1.83/1.26  ----------------------
% 1.83/1.26  Preprocessing        : 0.27
% 1.83/1.26  Parsing              : 0.15
% 1.83/1.26  CNF conversion       : 0.02
% 1.83/1.26  Main loop            : 0.13
% 1.83/1.26  Inferencing          : 0.06
% 1.83/1.26  Reduction            : 0.04
% 1.83/1.26  Demodulation         : 0.03
% 1.83/1.26  BG Simplification    : 0.01
% 1.83/1.26  Subsumption          : 0.02
% 1.83/1.26  Abstraction          : 0.01
% 1.83/1.26  MUC search           : 0.00
% 1.83/1.26  Cooper               : 0.00
% 1.83/1.26  Total                : 0.43
% 1.83/1.26  Index Insertion      : 0.00
% 1.83/1.26  Index Deletion       : 0.00
% 1.83/1.26  Index Matching       : 0.00
% 1.83/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
