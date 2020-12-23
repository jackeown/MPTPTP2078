%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:32 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
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
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_34,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_77,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( r1_tarski(C_6,A_2)
      | ~ r2_hidden(C_6,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [A_45,A_46] :
      ( r1_tarski(A_45,A_46)
      | v1_xboole_0(k1_zfmisc_1(A_46))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_46)) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_119,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,A_47)
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_43,c_110])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [C_37,B_38,A_39] :
      ( ~ v1_xboole_0(C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    ! [A_40,A_41] :
      ( ~ v1_xboole_0(A_40)
      | ~ r2_hidden(A_41,A_40) ) ),
    inference(resolution,[status(thm)],[c_43,c_83])).

tff(c_98,plain,(
    ! [A_2,C_6] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_123,plain,(
    ! [C_48,A_49] :
      ( ~ r1_tarski(C_48,A_49)
      | r1_tarski(A_49,A_49) ) ),
    inference(resolution,[status(thm)],[c_119,c_98])).

tff(c_129,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
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

tff(c_134,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_138,plain,(
    ! [C_53] : ~ r1_tarski(C_53,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_134,c_98])).

tff(c_146,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_129,c_138])).

tff(c_147,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_16] :
      ( k1_tops_1(A_16,k2_struct_0(A_16)) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_178,plain,(
    ! [C_60,A_61,B_62] :
      ( m2_connsp_2(C_60,A_61,B_62)
      | ~ r1_tarski(B_62,k1_tops_1(A_61,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_358,plain,(
    ! [A_88,B_89] :
      ( m2_connsp_2(k2_struct_0(A_88),A_88,B_89)
      | ~ r1_tarski(B_89,k2_struct_0(A_88))
      | ~ m1_subset_1(k2_struct_0(A_88),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_178])).

tff(c_360,plain,(
    ! [B_89] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_89)
      | ~ r1_tarski(B_89,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_358])).

tff(c_364,plain,(
    ! [B_90] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_90)
      | ~ r1_tarski(B_90,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_40,c_38,c_65,c_43,c_360])).

tff(c_367,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_364])).

tff(c_374,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_367])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.43  
% 2.46/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.43  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.46/1.43  
% 2.46/1.43  %Foreground sorts:
% 2.46/1.43  
% 2.46/1.43  
% 2.46/1.43  %Background operators:
% 2.46/1.43  
% 2.46/1.43  
% 2.46/1.43  %Foreground operators:
% 2.46/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.46/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.46/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.46/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.46/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.46/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.46/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.46/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.43  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.46/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.43  
% 2.46/1.45  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.46/1.45  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.46/1.45  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.46/1.45  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.46/1.45  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.46/1.45  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.46/1.45  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.46/1.45  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.46/1.45  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.46/1.45  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.46/1.45  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.46/1.45  tff(c_34, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.45  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.45  tff(c_16, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.46/1.45  tff(c_18, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.45  tff(c_43, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.46/1.45  tff(c_77, plain, (![A_35, B_36]: (r2_hidden(A_35, B_36) | v1_xboole_0(B_36) | ~m1_subset_1(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.45  tff(c_4, plain, (![C_6, A_2]: (r1_tarski(C_6, A_2) | ~r2_hidden(C_6, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.46/1.45  tff(c_110, plain, (![A_45, A_46]: (r1_tarski(A_45, A_46) | v1_xboole_0(k1_zfmisc_1(A_46)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_46)))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.46/1.45  tff(c_119, plain, (![A_47]: (r1_tarski(A_47, A_47) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_43, c_110])).
% 2.46/1.45  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.46/1.45  tff(c_83, plain, (![C_37, B_38, A_39]: (~v1_xboole_0(C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.45  tff(c_90, plain, (![A_40, A_41]: (~v1_xboole_0(A_40) | ~r2_hidden(A_41, A_40))), inference(resolution, [status(thm)], [c_43, c_83])).
% 2.46/1.45  tff(c_98, plain, (![A_2, C_6]: (~v1_xboole_0(k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.46/1.45  tff(c_123, plain, (![C_48, A_49]: (~r1_tarski(C_48, A_49) | r1_tarski(A_49, A_49))), inference(resolution, [status(thm)], [c_119, c_98])).
% 2.46/1.45  tff(c_129, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_2, c_123])).
% 2.46/1.45  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.45  tff(c_26, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.46/1.45  tff(c_56, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.45  tff(c_61, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.46/1.45  tff(c_65, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_61])).
% 2.46/1.45  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.45  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36])).
% 2.46/1.45  tff(c_117, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_110])).
% 2.46/1.45  tff(c_134, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_117])).
% 2.46/1.45  tff(c_138, plain, (![C_53]: (~r1_tarski(C_53, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_134, c_98])).
% 2.46/1.45  tff(c_146, plain, $false, inference(resolution, [status(thm)], [c_129, c_138])).
% 2.46/1.45  tff(c_147, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_117])).
% 2.46/1.45  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.45  tff(c_28, plain, (![A_16]: (k1_tops_1(A_16, k2_struct_0(A_16))=k2_struct_0(A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.45  tff(c_178, plain, (![C_60, A_61, B_62]: (m2_connsp_2(C_60, A_61, B_62) | ~r1_tarski(B_62, k1_tops_1(A_61, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.45  tff(c_358, plain, (![A_88, B_89]: (m2_connsp_2(k2_struct_0(A_88), A_88, B_89) | ~r1_tarski(B_89, k2_struct_0(A_88)) | ~m1_subset_1(k2_struct_0(A_88), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(superposition, [status(thm), theory('equality')], [c_28, c_178])).
% 2.46/1.45  tff(c_360, plain, (![B_89]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_89) | ~r1_tarski(B_89, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_358])).
% 2.46/1.45  tff(c_364, plain, (![B_90]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_90) | ~r1_tarski(B_90, k2_struct_0('#skF_3')) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_40, c_38, c_65, c_43, c_360])).
% 2.46/1.45  tff(c_367, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_364])).
% 2.46/1.45  tff(c_374, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_367])).
% 2.46/1.45  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_374])).
% 2.46/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.45  
% 2.46/1.45  Inference rules
% 2.46/1.45  ----------------------
% 2.46/1.45  #Ref     : 0
% 2.46/1.45  #Sup     : 68
% 2.46/1.45  #Fact    : 0
% 2.46/1.45  #Define  : 0
% 2.46/1.45  #Split   : 5
% 2.46/1.45  #Chain   : 0
% 2.46/1.45  #Close   : 0
% 2.46/1.45  
% 2.46/1.45  Ordering : KBO
% 2.46/1.45  
% 2.46/1.45  Simplification rules
% 2.46/1.45  ----------------------
% 2.46/1.45  #Subsume      : 6
% 2.46/1.45  #Demod        : 34
% 2.46/1.45  #Tautology    : 18
% 2.46/1.45  #SimpNegUnit  : 1
% 2.46/1.45  #BackRed      : 1
% 2.46/1.45  
% 2.46/1.45  #Partial instantiations: 0
% 2.46/1.45  #Strategies tried      : 1
% 2.46/1.45  
% 2.46/1.45  Timing (in seconds)
% 2.46/1.45  ----------------------
% 2.46/1.45  Preprocessing        : 0.33
% 2.46/1.45  Parsing              : 0.18
% 2.46/1.45  CNF conversion       : 0.02
% 2.46/1.45  Main loop            : 0.26
% 2.46/1.45  Inferencing          : 0.10
% 2.46/1.45  Reduction            : 0.08
% 2.46/1.45  Demodulation         : 0.05
% 2.46/1.45  BG Simplification    : 0.02
% 2.46/1.45  Subsumption          : 0.06
% 2.46/1.45  Abstraction          : 0.02
% 2.46/1.45  MUC search           : 0.00
% 2.46/1.45  Cooper               : 0.00
% 2.46/1.45  Total                : 0.63
% 2.46/1.45  Index Insertion      : 0.00
% 2.46/1.45  Index Deletion       : 0.00
% 2.46/1.45  Index Matching       : 0.00
% 2.46/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
