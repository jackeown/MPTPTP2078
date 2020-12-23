%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1385+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:53 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 10.49s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 365 expanded)
%              Number of leaves         :   36 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  226 (1167 expanded)
%              Number of equality atoms :   14 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_41,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_108,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_69,plain,(
    ~ m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))
    | m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_94,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_60])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_129,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_151,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_129])).

tff(c_173,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_32,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_177,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_32])).

tff(c_180,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_177])).

tff(c_183,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_183])).

tff(c_188,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_190,plain,(
    ~ m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_69])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_189,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_223,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k6_domain_1(A_81,B_82),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_232,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_223])).

tff(c_239,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_232])).

tff(c_240,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_239])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5858,plain,(
    ! [B_1595,A_1596,C_1597] :
      ( r2_hidden(B_1595,k1_tops_1(A_1596,C_1597))
      | ~ m1_connsp_2(C_1597,A_1596,B_1595)
      | ~ m1_subset_1(C_1597,k1_zfmisc_1(u1_struct_0(A_1596)))
      | ~ m1_subset_1(B_1595,u1_struct_0(A_1596))
      | ~ l1_pre_topc(A_1596)
      | ~ v2_pre_topc(A_1596)
      | v2_struct_0(A_1596) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5874,plain,(
    ! [B_1595] :
      ( r2_hidden(B_1595,k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1595)
      | ~ m1_subset_1(B_1595,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_5858])).

tff(c_5885,plain,(
    ! [B_1595] :
      ( r2_hidden(B_1595,k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1595)
      | ~ m1_subset_1(B_1595,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_5874])).

tff(c_5887,plain,(
    ! [B_1598] :
      ( r2_hidden(B_1598,k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1598)
      | ~ m1_subset_1(B_1598,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5885])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,B_32)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5907,plain,(
    ! [B_1598] :
      ( m1_subset_1(B_1598,k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1598)
      | ~ m1_subset_1(B_1598,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5887,c_36])).

tff(c_42,plain,(
    ! [B_36,A_35] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5908,plain,(
    ! [B_1598] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1598)
      | ~ m1_subset_1(B_1598,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5887,c_42])).

tff(c_5968,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5908])).

tff(c_6035,plain,(
    ! [B_1616] :
      ( m1_subset_1(B_1616,k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1616)
      | ~ m1_subset_1(B_1616,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5887,c_36])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( k6_domain_1(A_29,B_30) = k1_tarski(B_30)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6038,plain,(
    ! [B_1616] :
      ( k6_domain_1(k1_tops_1('#skF_4','#skF_6'),B_1616) = k1_tarski(B_1616)
      | v1_xboole_0(k1_tops_1('#skF_4','#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_4',B_1616)
      | ~ m1_subset_1(B_1616,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6035,c_34])).

tff(c_16051,plain,(
    ! [B_6034] :
      ( k6_domain_1(k1_tops_1('#skF_4','#skF_6'),B_6034) = k1_tarski(B_6034)
      | ~ m1_connsp_2('#skF_6','#skF_4',B_6034)
      | ~ m1_subset_1(B_6034,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5968,c_6038])).

tff(c_16082,plain,
    ( k6_domain_1(k1_tops_1('#skF_4','#skF_6'),'#skF_5') = k1_tarski('#skF_5')
    | ~ m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_16051])).

tff(c_16093,plain,(
    k6_domain_1(k1_tops_1('#skF_4','#skF_6'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16082])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_237,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k6_domain_1(A_81,B_82),A_81)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_223,c_38])).

tff(c_16100,plain,
    ( r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_6'))
    | v1_xboole_0(k1_tops_1('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16093,c_237])).

tff(c_16112,plain,
    ( r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_5968,c_16100])).

tff(c_16116,plain,(
    ~ m1_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_16112])).

tff(c_16176,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5907,c_16116])).

tff(c_16180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_94,c_16176])).

tff(c_16181,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_16112])).

tff(c_18,plain,(
    ! [C_19,A_13,B_17] :
      ( m2_connsp_2(C_19,A_13,B_17)
      | ~ r1_tarski(B_17,k1_tops_1(A_13,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16204,plain,
    ( m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16181,c_18])).

tff(c_16223,plain,(
    m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_240,c_44,c_16204])).

tff(c_16225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_16223])).

tff(c_16231,plain,(
    ! [B_6193] :
      ( ~ m1_connsp_2('#skF_6','#skF_4',B_6193)
      | ~ m1_subset_1(B_6193,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_5908])).

tff(c_16246,plain,(
    ~ m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_16231])).

tff(c_16253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16246])).

tff(c_16254,plain,(
    ~ m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_16353,plain,(
    ! [A_6222,B_6223] :
      ( k6_domain_1(A_6222,B_6223) = k1_tarski(B_6223)
      | ~ m1_subset_1(B_6223,A_6222)
      | v1_xboole_0(A_6222) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16375,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_16353])).

tff(c_16386,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16375])).

tff(c_16389,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16386,c_32])).

tff(c_16392,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_16389])).

tff(c_16395,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_16392])).

tff(c_16399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16395])).

tff(c_16400,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16375])).

tff(c_16268,plain,(
    m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_16254,c_60])).

tff(c_16402,plain,(
    m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16400,c_16268])).

tff(c_16401,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16375])).

tff(c_16408,plain,(
    ! [A_6229,B_6230] :
      ( m1_subset_1(k6_domain_1(A_6229,B_6230),k1_zfmisc_1(A_6229))
      | ~ m1_subset_1(B_6230,A_6229)
      | v1_xboole_0(A_6229) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16417,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16400,c_16408])).

tff(c_16424,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16417])).

tff(c_16425,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16401,c_16424])).

tff(c_21712,plain,(
    ! [B_7645,A_7646,C_7647] :
      ( r1_tarski(B_7645,k1_tops_1(A_7646,C_7647))
      | ~ m2_connsp_2(C_7647,A_7646,B_7645)
      | ~ m1_subset_1(C_7647,k1_zfmisc_1(u1_struct_0(A_7646)))
      | ~ m1_subset_1(B_7645,k1_zfmisc_1(u1_struct_0(A_7646)))
      | ~ l1_pre_topc(A_7646)
      | ~ v2_pre_topc(A_7646) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21728,plain,(
    ! [B_7645] :
      ( r1_tarski(B_7645,k1_tops_1('#skF_4','#skF_6'))
      | ~ m2_connsp_2('#skF_6','#skF_4',B_7645)
      | ~ m1_subset_1(B_7645,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_21712])).

tff(c_21957,plain,(
    ! [B_7673] :
      ( r1_tarski(B_7673,k1_tops_1('#skF_4','#skF_6'))
      | ~ m2_connsp_2('#skF_6','#skF_4',B_7673)
      | ~ m1_subset_1(B_7673,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_21728])).

tff(c_21968,plain,
    ( r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6'))
    | ~ m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16425,c_21957])).

tff(c_21988,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16402,c_21968])).

tff(c_8,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16303,plain,(
    ! [C_6211,B_6212,A_6213] :
      ( r2_hidden(C_6211,B_6212)
      | ~ r2_hidden(C_6211,A_6213)
      | ~ r1_tarski(A_6213,B_6212) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16309,plain,(
    ! [C_12,B_6212] :
      ( r2_hidden(C_12,B_6212)
      | ~ r1_tarski(k1_tarski(C_12),B_6212) ) ),
    inference(resolution,[status(thm)],[c_8,c_16303])).

tff(c_22006,plain,(
    r2_hidden('#skF_5',k1_tops_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_21988,c_16309])).

tff(c_2,plain,(
    ! [C_7,A_1,B_5] :
      ( m1_connsp_2(C_7,A_1,B_5)
      | ~ r2_hidden(B_5,k1_tops_1(A_1,C_7))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22008,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_22006,c_2])).

tff(c_22019,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_22008])).

tff(c_22021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_16254,c_22019])).

%------------------------------------------------------------------------------
