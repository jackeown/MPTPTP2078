%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:24 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   54 (  89 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 264 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_yellow19 > a_2_0_yellow19 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(a_2_0_yellow19,type,(
    a_2_0_yellow19: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_yellow19(A,B) = a_2_0_yellow19(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_yellow19(B,C))
      <=> ? [D] :
            ( m1_connsp_2(D,B,C)
            & A = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_35,plain,(
    ! [A_42,B_43] :
      ( k1_yellow19(A_42,B_43) = a_2_0_yellow19(A_42,B_43)
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,
    ( k1_yellow19('#skF_3','#skF_4') = a_2_0_yellow19('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_41,plain,
    ( k1_yellow19('#skF_3','#skF_4') = a_2_0_yellow19('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_38])).

tff(c_42,plain,(
    k1_yellow19('#skF_3','#skF_4') = a_2_0_yellow19('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_41])).

tff(c_22,plain,(
    ~ r2_waybel_7('#skF_3',k1_yellow19('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_43,plain,(
    ~ r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

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

tff(c_12,plain,(
    ! [A_8,B_15,C_16] :
      ( m1_subset_1('#skF_1'(A_8,B_15,C_16),k1_zfmisc_1(u1_struct_0(A_8)))
      | r2_waybel_7(A_8,B_15,C_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,(
    ! [B_60,A_61,C_62] :
      ( m1_connsp_2(B_60,A_61,C_62)
      | ~ r2_hidden(C_62,B_60)
      | ~ v3_pre_topc(B_60,A_61)
      | ~ m1_subset_1(C_62,u1_struct_0(A_61))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,(
    ! [B_60] :
      ( m1_connsp_2(B_60,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_60)
      | ~ v3_pre_topc(B_60,'#skF_3')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_76,plain,(
    ! [B_60] :
      ( m1_connsp_2(B_60,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_60)
      | ~ v3_pre_topc(B_60,'#skF_3')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_73])).

tff(c_78,plain,(
    ! [B_63] :
      ( m1_connsp_2(B_63,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_63)
      | ~ v3_pre_topc(B_63,'#skF_3')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_76])).

tff(c_82,plain,(
    ! [B_15,C_16] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_15,C_16),'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_3',B_15,C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_15,C_16),'#skF_3')
      | r2_waybel_7('#skF_3',B_15,C_16)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_85,plain,(
    ! [B_15,C_16] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_15,C_16),'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_3',B_15,C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_15,C_16),'#skF_3')
      | r2_waybel_7('#skF_3',B_15,C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_82])).

tff(c_48,plain,(
    ! [D_44,B_45,C_46] :
      ( r2_hidden(D_44,a_2_0_yellow19(B_45,C_46))
      | ~ m1_connsp_2(D_44,B_45,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(B_45))
      | ~ l1_pre_topc(B_45)
      | ~ v2_pre_topc(B_45)
      | v2_struct_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_8,B_15,C_16] :
      ( ~ r2_hidden('#skF_1'(A_8,B_15,C_16),B_15)
      | r2_waybel_7(A_8,B_15,C_16)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_146,plain,(
    ! [A_76,B_77,C_78,C_79] :
      ( r2_waybel_7(A_76,a_2_0_yellow19(B_77,C_78),C_79)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | ~ m1_connsp_2('#skF_1'(A_76,a_2_0_yellow19(B_77,C_78),C_79),B_77,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(B_77))
      | ~ l1_pre_topc(B_77)
      | ~ v2_pre_topc(B_77)
      | v2_struct_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_48,c_6])).

tff(c_150,plain,(
    ! [C_16] :
      ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16),'#skF_3')
      | r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16) ) ),
    inference(resolution,[status(thm)],[c_85,c_146])).

tff(c_153,plain,(
    ! [C_16] :
      ( v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16))
      | ~ v3_pre_topc('#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16),'#skF_3')
      | r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_150])).

tff(c_193,plain,(
    ! [C_84] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_84))
      | ~ v3_pre_topc('#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_84),'#skF_3')
      | r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_153])).

tff(c_197,plain,(
    ! [C_16] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16))
      | r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_16)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_193])).

tff(c_201,plain,(
    ! [C_85] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_85))
      | r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_197])).

tff(c_205,plain,
    ( r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_208,plain,(
    r2_waybel_7('#skF_3',a_2_0_yellow19('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_205])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.34  
% 2.04/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.35  %$ r2_waybel_7 > m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_yellow19 > a_2_0_yellow19 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.04/1.35  
% 2.04/1.35  %Foreground sorts:
% 2.04/1.35  
% 2.04/1.35  
% 2.04/1.35  %Background operators:
% 2.04/1.35  
% 2.04/1.35  
% 2.04/1.35  %Foreground operators:
% 2.04/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.35  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.04/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.04/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.04/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.35  tff(k1_yellow19, type, k1_yellow19: ($i * $i) > $i).
% 2.04/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.35  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.04/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.04/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.35  tff(a_2_0_yellow19, type, a_2_0_yellow19: ($i * $i) > $i).
% 2.04/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.35  
% 2.04/1.36  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_waybel_7(A, k1_yellow19(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_yellow19)).
% 2.04/1.36  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_yellow19(A, B) = a_2_0_yellow19(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow19)).
% 2.04/1.36  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (r2_waybel_7(A, B, C) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(D, A) & r2_hidden(C, D)) => r2_hidden(D, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_waybel_7)).
% 2.04/1.36  tff(f_44, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.04/1.36  tff(f_88, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_subset_1(C, u1_struct_0(B))) => (r2_hidden(A, a_2_0_yellow19(B, C)) <=> (?[D]: (m1_connsp_2(D, B, C) & (A = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_yellow19)).
% 2.04/1.36  tff(c_30, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.04/1.36  tff(c_28, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.04/1.36  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.04/1.36  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.04/1.36  tff(c_35, plain, (![A_42, B_43]: (k1_yellow19(A_42, B_43)=a_2_0_yellow19(A_42, B_43) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.36  tff(c_38, plain, (k1_yellow19('#skF_3', '#skF_4')=a_2_0_yellow19('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.04/1.36  tff(c_41, plain, (k1_yellow19('#skF_3', '#skF_4')=a_2_0_yellow19('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_38])).
% 2.04/1.36  tff(c_42, plain, (k1_yellow19('#skF_3', '#skF_4')=a_2_0_yellow19('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_41])).
% 2.04/1.36  tff(c_22, plain, (~r2_waybel_7('#skF_3', k1_yellow19('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.04/1.36  tff(c_43, plain, (~r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 2.04/1.36  tff(c_8, plain, (![C_16, A_8, B_15]: (r2_hidden(C_16, '#skF_1'(A_8, B_15, C_16)) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.04/1.36  tff(c_10, plain, (![A_8, B_15, C_16]: (v3_pre_topc('#skF_1'(A_8, B_15, C_16), A_8) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.04/1.36  tff(c_12, plain, (![A_8, B_15, C_16]: (m1_subset_1('#skF_1'(A_8, B_15, C_16), k1_zfmisc_1(u1_struct_0(A_8))) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.04/1.36  tff(c_71, plain, (![B_60, A_61, C_62]: (m1_connsp_2(B_60, A_61, C_62) | ~r2_hidden(C_62, B_60) | ~v3_pre_topc(B_60, A_61) | ~m1_subset_1(C_62, u1_struct_0(A_61)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.36  tff(c_73, plain, (![B_60]: (m1_connsp_2(B_60, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_60) | ~v3_pre_topc(B_60, '#skF_3') | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_71])).
% 2.04/1.36  tff(c_76, plain, (![B_60]: (m1_connsp_2(B_60, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_60) | ~v3_pre_topc(B_60, '#skF_3') | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_73])).
% 2.04/1.36  tff(c_78, plain, (![B_63]: (m1_connsp_2(B_63, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_63) | ~v3_pre_topc(B_63, '#skF_3') | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_76])).
% 2.04/1.36  tff(c_82, plain, (![B_15, C_16]: (m1_connsp_2('#skF_1'('#skF_3', B_15, C_16), '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', '#skF_1'('#skF_3', B_15, C_16)) | ~v3_pre_topc('#skF_1'('#skF_3', B_15, C_16), '#skF_3') | r2_waybel_7('#skF_3', B_15, C_16) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_78])).
% 2.04/1.36  tff(c_85, plain, (![B_15, C_16]: (m1_connsp_2('#skF_1'('#skF_3', B_15, C_16), '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', '#skF_1'('#skF_3', B_15, C_16)) | ~v3_pre_topc('#skF_1'('#skF_3', B_15, C_16), '#skF_3') | r2_waybel_7('#skF_3', B_15, C_16))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_82])).
% 2.04/1.36  tff(c_48, plain, (![D_44, B_45, C_46]: (r2_hidden(D_44, a_2_0_yellow19(B_45, C_46)) | ~m1_connsp_2(D_44, B_45, C_46) | ~m1_subset_1(C_46, u1_struct_0(B_45)) | ~l1_pre_topc(B_45) | ~v2_pre_topc(B_45) | v2_struct_0(B_45))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.36  tff(c_6, plain, (![A_8, B_15, C_16]: (~r2_hidden('#skF_1'(A_8, B_15, C_16), B_15) | r2_waybel_7(A_8, B_15, C_16) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.04/1.36  tff(c_146, plain, (![A_76, B_77, C_78, C_79]: (r2_waybel_7(A_76, a_2_0_yellow19(B_77, C_78), C_79) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | ~m1_connsp_2('#skF_1'(A_76, a_2_0_yellow19(B_77, C_78), C_79), B_77, C_78) | ~m1_subset_1(C_78, u1_struct_0(B_77)) | ~l1_pre_topc(B_77) | ~v2_pre_topc(B_77) | v2_struct_0(B_77))), inference(resolution, [status(thm)], [c_48, c_6])).
% 2.04/1.36  tff(c_150, plain, (![C_16]: (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_4', '#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16)) | ~v3_pre_topc('#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16), '#skF_3') | r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16))), inference(resolution, [status(thm)], [c_85, c_146])).
% 2.04/1.36  tff(c_153, plain, (![C_16]: (v2_struct_0('#skF_3') | ~r2_hidden('#skF_4', '#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16)) | ~v3_pre_topc('#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16), '#skF_3') | r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_150])).
% 2.04/1.36  tff(c_193, plain, (![C_84]: (~r2_hidden('#skF_4', '#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_84)) | ~v3_pre_topc('#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_84), '#skF_3') | r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_84))), inference(negUnitSimplification, [status(thm)], [c_30, c_153])).
% 2.04/1.36  tff(c_197, plain, (![C_16]: (~r2_hidden('#skF_4', '#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16)) | r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_16) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_193])).
% 2.04/1.36  tff(c_201, plain, (![C_85]: (~r2_hidden('#skF_4', '#skF_1'('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_85)) | r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), C_85))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_197])).
% 2.04/1.36  tff(c_205, plain, (r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_201])).
% 2.04/1.36  tff(c_208, plain, (r2_waybel_7('#skF_3', a_2_0_yellow19('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_205])).
% 2.04/1.36  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_208])).
% 2.04/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.36  
% 2.04/1.36  Inference rules
% 2.04/1.36  ----------------------
% 2.04/1.36  #Ref     : 0
% 2.04/1.36  #Sup     : 31
% 2.04/1.36  #Fact    : 0
% 2.04/1.36  #Define  : 0
% 2.04/1.36  #Split   : 0
% 2.04/1.36  #Chain   : 0
% 2.04/1.36  #Close   : 0
% 2.04/1.36  
% 2.04/1.36  Ordering : KBO
% 2.04/1.36  
% 2.04/1.36  Simplification rules
% 2.04/1.36  ----------------------
% 2.04/1.36  #Subsume      : 2
% 2.04/1.36  #Demod        : 35
% 2.04/1.36  #Tautology    : 11
% 2.04/1.36  #SimpNegUnit  : 10
% 2.04/1.36  #BackRed      : 1
% 2.04/1.36  
% 2.04/1.36  #Partial instantiations: 0
% 2.04/1.36  #Strategies tried      : 1
% 2.04/1.36  
% 2.04/1.36  Timing (in seconds)
% 2.04/1.36  ----------------------
% 2.04/1.37  Preprocessing        : 0.30
% 2.04/1.37  Parsing              : 0.16
% 2.04/1.37  CNF conversion       : 0.02
% 2.04/1.37  Main loop            : 0.19
% 2.04/1.37  Inferencing          : 0.08
% 2.04/1.37  Reduction            : 0.05
% 2.04/1.37  Demodulation         : 0.04
% 2.04/1.37  BG Simplification    : 0.01
% 2.04/1.37  Subsumption          : 0.03
% 2.04/1.37  Abstraction          : 0.01
% 2.04/1.37  MUC search           : 0.00
% 2.04/1.37  Cooper               : 0.00
% 2.04/1.37  Total                : 0.52
% 2.04/1.37  Index Insertion      : 0.00
% 2.04/1.37  Index Deletion       : 0.00
% 2.04/1.37  Index Matching       : 0.00
% 2.04/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
