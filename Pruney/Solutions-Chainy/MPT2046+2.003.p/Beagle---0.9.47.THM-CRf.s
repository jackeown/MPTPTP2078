%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:24 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   46 (  73 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 221 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_yellow19,type,(
    k1_yellow19: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( r2_waybel_7(A,B,C)
        <=> ! [D] :
              ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(D,A)
                  & r2_hidden(C,D) )
               => r2_hidden(D,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

tff(f_44,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(C,k1_yellow19(A,B))
            <=> m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

tff(c_18,plain,(
    ~ r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [C_16,A_8,B_15] :
      ( r2_hidden(C_16,'#skF_1'(A_8,B_15,C_16))
      | r2_waybel_7(A_8,B_15,C_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_8,B_15,C_16] :
      ( v3_pre_topc('#skF_1'(A_8,B_15,C_16),A_8)
      | r2_waybel_7(A_8,B_15,C_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_8,B_15,C_16] :
      ( m1_subset_1('#skF_1'(A_8,B_15,C_16),k1_zfmisc_1(u1_struct_0(A_8)))
      | r2_waybel_7(A_8,B_15,C_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    ! [B_50,A_51,C_52] :
      ( m1_connsp_2(B_50,A_51,C_52)
      | ~ r2_hidden(C_52,B_50)
      | ~ v3_pre_topc(B_50,A_51)
      | ~ m1_subset_1(C_52,u1_struct_0(A_51))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    ! [B_50] :
      ( m1_connsp_2(B_50,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_50)
      | ~ v3_pre_topc(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_54,plain,(
    ! [B_50] :
      ( m1_connsp_2(B_50,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_50)
      | ~ v3_pre_topc(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_51])).

tff(c_56,plain,(
    ! [B_53] :
      ( m1_connsp_2(B_53,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_53)
      | ~ v3_pre_topc(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_54])).

tff(c_60,plain,(
    ! [B_15,C_16] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_15,C_16),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_15,C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_15,C_16),'#skF_2')
      | r2_waybel_7('#skF_2',B_15,C_16)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_56])).

tff(c_63,plain,(
    ! [B_15,C_16] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_15,C_16),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_15,C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_15,C_16),'#skF_2')
      | r2_waybel_7('#skF_2',B_15,C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_60])).

tff(c_32,plain,(
    ! [C_43,A_44,B_45] :
      ( r2_hidden(C_43,k1_yellow19(A_44,B_45))
      | ~ m1_connsp_2(C_43,A_44,B_45)
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_8,B_15,C_16] :
      ( ~ r2_hidden('#skF_1'(A_8,B_15,C_16),B_15)
      | r2_waybel_7(A_8,B_15,C_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ! [A_56,A_57,B_58,C_59] :
      ( r2_waybel_7(A_56,k1_yellow19(A_57,B_58),C_59)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_connsp_2('#skF_1'(A_56,k1_yellow19(A_57,B_58),C_59),A_57,B_58)
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_32,c_6])).

tff(c_69,plain,(
    ! [C_16] :
      ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16),'#skF_2')
      | r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16) ) ),
    inference(resolution,[status(thm)],[c_63,c_65])).

tff(c_72,plain,(
    ! [C_16] :
      ( v2_struct_0('#skF_2')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16),'#skF_2')
      | r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_69])).

tff(c_74,plain,(
    ! [C_60] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_60))
      | ~ v3_pre_topc('#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_60),'#skF_2')
      | r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_60) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_72])).

tff(c_78,plain,(
    ! [C_16] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16))
      | r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_16)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_82,plain,(
    ! [C_61] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_61))
      | r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),C_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_78])).

tff(c_86,plain,
    ( r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_89,plain,(
    r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  %$ r2_waybel_7 > m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 1.85/1.21  
% 1.85/1.21  %Foreground sorts:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Background operators:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Foreground operators:
% 1.85/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.85/1.21  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 1.85/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.21  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.21  tff(k1_yellow19, type, k1_yellow19: ($i * $i) > $i).
% 1.85/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.85/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.21  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.85/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.85/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.21  
% 1.85/1.23  tff(f_88, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_waybel_7(A, k1_yellow19(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_yellow19)).
% 1.85/1.23  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (r2_waybel_7(A, B, C) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(D, A) & r2_hidden(C, D)) => r2_hidden(D, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_waybel_7)).
% 1.85/1.23  tff(f_44, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 1.85/1.23  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(C, k1_yellow19(A, B)) <=> m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow19)).
% 1.85/1.23  tff(c_18, plain, (~r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.85/1.23  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.85/1.23  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.85/1.23  tff(c_8, plain, (![C_16, A_8, B_15]: (r2_hidden(C_16, '#skF_1'(A_8, B_15, C_16)) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.23  tff(c_10, plain, (![A_8, B_15, C_16]: (v3_pre_topc('#skF_1'(A_8, B_15, C_16), A_8) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.23  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.85/1.23  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.85/1.23  tff(c_12, plain, (![A_8, B_15, C_16]: (m1_subset_1('#skF_1'(A_8, B_15, C_16), k1_zfmisc_1(u1_struct_0(A_8))) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.23  tff(c_49, plain, (![B_50, A_51, C_52]: (m1_connsp_2(B_50, A_51, C_52) | ~r2_hidden(C_52, B_50) | ~v3_pre_topc(B_50, A_51) | ~m1_subset_1(C_52, u1_struct_0(A_51)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.23  tff(c_51, plain, (![B_50]: (m1_connsp_2(B_50, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_50) | ~v3_pre_topc(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_49])).
% 1.85/1.23  tff(c_54, plain, (![B_50]: (m1_connsp_2(B_50, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_50) | ~v3_pre_topc(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_51])).
% 1.85/1.23  tff(c_56, plain, (![B_53]: (m1_connsp_2(B_53, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_53) | ~v3_pre_topc(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_54])).
% 1.85/1.23  tff(c_60, plain, (![B_15, C_16]: (m1_connsp_2('#skF_1'('#skF_2', B_15, C_16), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_15, C_16)) | ~v3_pre_topc('#skF_1'('#skF_2', B_15, C_16), '#skF_2') | r2_waybel_7('#skF_2', B_15, C_16) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_56])).
% 1.85/1.23  tff(c_63, plain, (![B_15, C_16]: (m1_connsp_2('#skF_1'('#skF_2', B_15, C_16), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_15, C_16)) | ~v3_pre_topc('#skF_1'('#skF_2', B_15, C_16), '#skF_2') | r2_waybel_7('#skF_2', B_15, C_16))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_60])).
% 1.85/1.23  tff(c_32, plain, (![C_43, A_44, B_45]: (r2_hidden(C_43, k1_yellow19(A_44, B_45)) | ~m1_connsp_2(C_43, A_44, B_45) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.85/1.23  tff(c_6, plain, (![A_8, B_15, C_16]: (~r2_hidden('#skF_1'(A_8, B_15, C_16), B_15) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.23  tff(c_65, plain, (![A_56, A_57, B_58, C_59]: (r2_waybel_7(A_56, k1_yellow19(A_57, B_58), C_59) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | ~m1_connsp_2('#skF_1'(A_56, k1_yellow19(A_57, B_58), C_59), A_57, B_58) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_32, c_6])).
% 1.85/1.23  tff(c_69, plain, (![C_16]: (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16)) | ~v3_pre_topc('#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16), '#skF_2') | r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16))), inference(resolution, [status(thm)], [c_63, c_65])).
% 1.85/1.23  tff(c_72, plain, (![C_16]: (v2_struct_0('#skF_2') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16)) | ~v3_pre_topc('#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16), '#skF_2') | r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_69])).
% 1.85/1.23  tff(c_74, plain, (![C_60]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_60)) | ~v3_pre_topc('#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_60), '#skF_2') | r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_60))), inference(negUnitSimplification, [status(thm)], [c_26, c_72])).
% 1.85/1.23  tff(c_78, plain, (![C_16]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16)) | r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_16) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_74])).
% 1.85/1.23  tff(c_82, plain, (![C_61]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_61)) | r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), C_61))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_78])).
% 1.85/1.23  tff(c_86, plain, (r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_82])).
% 1.85/1.23  tff(c_89, plain, (r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_86])).
% 1.85/1.23  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_89])).
% 1.85/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.23  
% 1.85/1.23  Inference rules
% 1.85/1.23  ----------------------
% 1.85/1.23  #Ref     : 0
% 1.85/1.23  #Sup     : 9
% 1.85/1.23  #Fact    : 0
% 1.85/1.23  #Define  : 0
% 1.85/1.23  #Split   : 0
% 1.85/1.23  #Chain   : 0
% 1.85/1.23  #Close   : 0
% 1.85/1.23  
% 1.85/1.23  Ordering : KBO
% 1.85/1.23  
% 1.85/1.23  Simplification rules
% 1.85/1.23  ----------------------
% 1.85/1.23  #Subsume      : 1
% 1.85/1.23  #Demod        : 11
% 1.85/1.23  #Tautology    : 1
% 1.85/1.23  #SimpNegUnit  : 3
% 1.85/1.23  #BackRed      : 0
% 1.85/1.23  
% 1.85/1.23  #Partial instantiations: 0
% 1.85/1.23  #Strategies tried      : 1
% 1.85/1.23  
% 1.85/1.23  Timing (in seconds)
% 1.85/1.23  ----------------------
% 1.85/1.23  Preprocessing        : 0.26
% 1.85/1.23  Parsing              : 0.15
% 1.85/1.23  CNF conversion       : 0.02
% 1.85/1.23  Main loop            : 0.14
% 1.85/1.23  Inferencing          : 0.07
% 1.85/1.23  Reduction            : 0.04
% 1.85/1.23  Demodulation         : 0.03
% 1.85/1.23  BG Simplification    : 0.01
% 1.85/1.23  Subsumption          : 0.02
% 1.85/1.23  Abstraction          : 0.01
% 1.85/1.23  MUC search           : 0.00
% 1.85/1.23  Cooper               : 0.00
% 1.85/1.23  Total                : 0.43
% 1.85/1.23  Index Insertion      : 0.00
% 1.85/1.23  Index Deletion       : 0.00
% 1.85/1.23  Index Matching       : 0.00
% 1.85/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
