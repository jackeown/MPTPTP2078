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
% DateTime   : Thu Dec  3 10:24:32 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 149 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 284 expanded)
%              Number of equality atoms :    9 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_79,axiom,(
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

tff(c_34,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_77,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [A_47,A_48] :
      ( r1_tarski(A_47,A_48)
      | v1_xboole_0(k1_zfmisc_1(A_48))
      | ~ m1_subset_1(A_47,k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_119,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,A_49)
      | v1_xboole_0(k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_43,c_110])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    ! [A_42,A_43] :
      ( ~ v1_xboole_0(A_42)
      | ~ r2_hidden(A_43,A_42) ) ),
    inference(resolution,[status(thm)],[c_43,c_83])).

tff(c_98,plain,(
    ! [A_3,C_7] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_123,plain,(
    ! [C_50,A_51] :
      ( ~ r1_tarski(C_50,A_51)
      | r1_tarski(A_51,A_51) ) ),
    inference(resolution,[status(thm)],[c_119,c_98])).

tff(c_129,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_65,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_61])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_36])).

tff(c_117,plain,
    ( r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_66,c_110])).

tff(c_143,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_147,plain,(
    ! [C_55] : ~ r1_tarski(C_55,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_143,c_98])).

tff(c_155,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_129,c_147])).

tff(c_156,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_17] :
      ( k1_tops_1(A_17,k2_struct_0(A_17)) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_178,plain,(
    ! [C_62,A_63,B_64] :
      ( m2_connsp_2(C_62,A_63,B_64)
      | ~ r1_tarski(B_64,k1_tops_1(A_63,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_383,plain,(
    ! [A_99,B_100] :
      ( m2_connsp_2(k2_struct_0(A_99),A_99,B_100)
      | ~ r1_tarski(B_100,k2_struct_0(A_99))
      | ~ m1_subset_1(k2_struct_0(A_99),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_178])).

tff(c_385,plain,(
    ! [B_100] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_100)
      | ~ r1_tarski(B_100,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_383])).

tff(c_388,plain,(
    ! [B_101] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_101)
      | ~ r1_tarski(B_101,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_40,c_38,c_65,c_43,c_385])).

tff(c_391,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_388])).

tff(c_398,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_391])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:03:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.33  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.50/1.33  
% 2.50/1.33  %Foreground sorts:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Background operators:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Foreground operators:
% 2.50/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.50/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.50/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.50/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.33  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.50/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.33  
% 2.50/1.34  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.50/1.34  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.50/1.34  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.50/1.34  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.50/1.34  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.50/1.34  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.50/1.34  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.50/1.34  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.50/1.34  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.50/1.34  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.50/1.34  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.50/1.34  tff(c_34, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.50/1.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.34  tff(c_16, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.50/1.34  tff(c_18, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.34  tff(c_43, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.50/1.34  tff(c_77, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.34  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.34  tff(c_110, plain, (![A_47, A_48]: (r1_tarski(A_47, A_48) | v1_xboole_0(k1_zfmisc_1(A_48)) | ~m1_subset_1(A_47, k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.50/1.34  tff(c_119, plain, (![A_49]: (r1_tarski(A_49, A_49) | v1_xboole_0(k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_43, c_110])).
% 2.50/1.34  tff(c_6, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.34  tff(c_83, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.50/1.34  tff(c_90, plain, (![A_42, A_43]: (~v1_xboole_0(A_42) | ~r2_hidden(A_43, A_42))), inference(resolution, [status(thm)], [c_43, c_83])).
% 2.50/1.34  tff(c_98, plain, (![A_3, C_7]: (~v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.50/1.34  tff(c_123, plain, (![C_50, A_51]: (~r1_tarski(C_50, A_51) | r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_119, c_98])).
% 2.50/1.34  tff(c_129, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_2, c_123])).
% 2.50/1.34  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.50/1.34  tff(c_26, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.34  tff(c_56, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.50/1.34  tff(c_61, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.50/1.34  tff(c_65, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_61])).
% 2.50/1.34  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.50/1.34  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36])).
% 2.50/1.34  tff(c_117, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_110])).
% 2.50/1.34  tff(c_143, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_117])).
% 2.50/1.34  tff(c_147, plain, (![C_55]: (~r1_tarski(C_55, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_143, c_98])).
% 2.50/1.34  tff(c_155, plain, $false, inference(resolution, [status(thm)], [c_129, c_147])).
% 2.50/1.34  tff(c_156, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_117])).
% 2.50/1.34  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.50/1.34  tff(c_28, plain, (![A_17]: (k1_tops_1(A_17, k2_struct_0(A_17))=k2_struct_0(A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.34  tff(c_178, plain, (![C_62, A_63, B_64]: (m2_connsp_2(C_62, A_63, B_64) | ~r1_tarski(B_64, k1_tops_1(A_63, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.50/1.34  tff(c_383, plain, (![A_99, B_100]: (m2_connsp_2(k2_struct_0(A_99), A_99, B_100) | ~r1_tarski(B_100, k2_struct_0(A_99)) | ~m1_subset_1(k2_struct_0(A_99), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99))), inference(superposition, [status(thm), theory('equality')], [c_28, c_178])).
% 2.50/1.34  tff(c_385, plain, (![B_100]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_100) | ~r1_tarski(B_100, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_383])).
% 2.50/1.34  tff(c_388, plain, (![B_101]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_101) | ~r1_tarski(B_101, k2_struct_0('#skF_3')) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_40, c_38, c_65, c_43, c_385])).
% 2.50/1.34  tff(c_391, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_388])).
% 2.50/1.34  tff(c_398, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_391])).
% 2.50/1.34  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_398])).
% 2.50/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  Inference rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Ref     : 0
% 2.50/1.34  #Sup     : 73
% 2.50/1.34  #Fact    : 0
% 2.50/1.34  #Define  : 0
% 2.50/1.34  #Split   : 4
% 2.50/1.34  #Chain   : 0
% 2.50/1.34  #Close   : 0
% 2.50/1.34  
% 2.50/1.34  Ordering : KBO
% 2.50/1.34  
% 2.50/1.34  Simplification rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Subsume      : 5
% 2.50/1.34  #Demod        : 45
% 2.50/1.34  #Tautology    : 18
% 2.50/1.34  #SimpNegUnit  : 1
% 2.50/1.34  #BackRed      : 1
% 2.50/1.34  
% 2.50/1.34  #Partial instantiations: 0
% 2.50/1.34  #Strategies tried      : 1
% 2.50/1.34  
% 2.50/1.34  Timing (in seconds)
% 2.50/1.34  ----------------------
% 2.50/1.35  Preprocessing        : 0.31
% 2.50/1.35  Parsing              : 0.16
% 2.50/1.35  CNF conversion       : 0.02
% 2.50/1.35  Main loop            : 0.29
% 2.50/1.35  Inferencing          : 0.11
% 2.50/1.35  Reduction            : 0.08
% 2.50/1.35  Demodulation         : 0.06
% 2.50/1.35  BG Simplification    : 0.02
% 2.50/1.35  Subsumption          : 0.06
% 2.50/1.35  Abstraction          : 0.02
% 2.50/1.35  MUC search           : 0.00
% 2.50/1.35  Cooper               : 0.00
% 2.50/1.35  Total                : 0.63
% 2.50/1.35  Index Insertion      : 0.00
% 2.50/1.35  Index Deletion       : 0.00
% 2.50/1.35  Index Matching       : 0.00
% 2.50/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
