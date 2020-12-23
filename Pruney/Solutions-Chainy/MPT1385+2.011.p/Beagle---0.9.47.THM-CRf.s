%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:16 EST 2020

% Result     : Theorem 13.87s
% Output     : CNFRefutation 14.06s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 576 expanded)
%              Number of leaves         :   38 ( 207 expanded)
%              Depth                    :   15
%              Number of atoms          :  336 (1663 expanded)
%              Number of equality atoms :   17 (  91 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_106,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_120,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_34,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_89,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_142,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ v1_xboole_0(C_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(C_75))
      | ~ r2_hidden(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_151,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_77,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_142])).

tff(c_152,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_153,plain,(
    ! [A_78,B_79] :
      ( k6_domain_1(A_78,B_79) = k1_tarski(B_79)
      | ~ m1_subset_1(B_79,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_169,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_153])).

tff(c_188,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_169])).

tff(c_64,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_110,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64])).

tff(c_189,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_110])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_271,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k6_domain_1(A_104,B_105),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_284,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_271])).

tff(c_290,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_284])).

tff(c_291,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_290])).

tff(c_5900,plain,(
    ! [B_6113,A_6114,C_6115] :
      ( r2_hidden(B_6113,k1_tops_1(A_6114,C_6115))
      | ~ m1_connsp_2(C_6115,A_6114,B_6113)
      | ~ m1_subset_1(C_6115,k1_zfmisc_1(u1_struct_0(A_6114)))
      | ~ m1_subset_1(B_6113,u1_struct_0(A_6114))
      | ~ l1_pre_topc(A_6114)
      | ~ v2_pre_topc(A_6114)
      | v2_struct_0(A_6114) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5921,plain,(
    ! [B_6113] :
      ( r2_hidden(B_6113,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6113)
      | ~ m1_subset_1(B_6113,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_5900])).

tff(c_5935,plain,(
    ! [B_6113] :
      ( r2_hidden(B_6113,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6113)
      | ~ m1_subset_1(B_6113,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5921])).

tff(c_5937,plain,(
    ! [B_6161] :
      ( r2_hidden(B_6161,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6161)
      | ~ m1_subset_1(B_6161,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5935])).

tff(c_103,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k1_tarski(A_64),k1_zfmisc_1(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_103,c_26])).

tff(c_74,plain,(
    ! [A_57] : k2_tarski(A_57,A_57) = k1_tarski(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_57] : r2_hidden(A_57,k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_215,plain,(
    ! [A_90,C_91,B_92] :
      ( m1_subset_1(A_90,C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_90,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_236,plain,(
    ! [A_97,B_98,A_99] :
      ( m1_subset_1(A_97,B_98)
      | ~ r2_hidden(A_97,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_249,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(A_100,B_101)
      | ~ r1_tarski(k1_tarski(A_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_80,c_236])).

tff(c_253,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(A_64,B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_107,c_249])).

tff(c_5967,plain,(
    ! [B_6161] :
      ( m1_subset_1(B_6161,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6161)
      | ~ m1_subset_1(B_6161,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5937,c_253])).

tff(c_5394,plain,(
    ! [B_5369,A_5370,C_5371] :
      ( r1_tarski(B_5369,k1_tops_1(A_5370,C_5371))
      | ~ m2_connsp_2(C_5371,A_5370,B_5369)
      | ~ m1_subset_1(C_5371,k1_zfmisc_1(u1_struct_0(A_5370)))
      | ~ m1_subset_1(B_5369,k1_zfmisc_1(u1_struct_0(A_5370)))
      | ~ l1_pre_topc(A_5370)
      | ~ v2_pre_topc(A_5370) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5415,plain,(
    ! [B_5369] :
      ( r1_tarski(B_5369,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_5369)
      | ~ m1_subset_1(B_5369,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_5394])).

tff(c_5428,plain,(
    ! [B_5417] :
      ( r1_tarski(B_5417,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_5417)
      | ~ m1_subset_1(B_5417,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5415])).

tff(c_5463,plain,(
    ! [A_5508] :
      ( r1_tarski(A_5508,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',A_5508)
      | ~ r1_tarski(A_5508,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_28,c_5428])).

tff(c_170,plain,(
    ! [B_80,A_81,A_82] :
      ( ~ v1_xboole_0(B_80)
      | ~ r2_hidden(A_81,A_82)
      | ~ r1_tarski(A_82,B_80) ) ),
    inference(resolution,[status(thm)],[c_28,c_142])).

tff(c_180,plain,(
    ! [B_80,A_57] :
      ( ~ v1_xboole_0(B_80)
      | ~ r1_tarski(k1_tarski(A_57),B_80) ) ),
    inference(resolution,[status(thm)],[c_80,c_170])).

tff(c_5495,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_57))
      | ~ r1_tarski(k1_tarski(A_57),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5463,c_180])).

tff(c_5496,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5495])).

tff(c_5971,plain,(
    ! [B_6207] :
      ( m1_subset_1(B_6207,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6207)
      | ~ m1_subset_1(B_6207,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5937,c_253])).

tff(c_40,plain,(
    ! [A_24,B_25] :
      ( k6_domain_1(A_24,B_25) = k1_tarski(B_25)
      | ~ m1_subset_1(B_25,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5976,plain,(
    ! [B_6207] :
      ( k6_domain_1(k1_tops_1('#skF_3','#skF_5'),B_6207) = k1_tarski(B_6207)
      | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6207)
      | ~ m1_subset_1(B_6207,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5971,c_40])).

tff(c_6286,plain,(
    ! [B_6669] :
      ( k6_domain_1(k1_tops_1('#skF_3','#skF_5'),B_6669) = k1_tarski(B_6669)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_6669)
      | ~ m1_subset_1(B_6669,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5496,c_5976])).

tff(c_6307,plain,
    ( k6_domain_1(k1_tops_1('#skF_3','#skF_5'),'#skF_4') = k1_tarski('#skF_4')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6286])).

tff(c_6312,plain,(
    k6_domain_1(k1_tops_1('#skF_3','#skF_5'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_6307])).

tff(c_288,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k6_domain_1(A_104,B_105),A_104)
      | ~ m1_subset_1(B_105,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_271,c_26])).

tff(c_6319,plain,
    ( r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6312,c_288])).

tff(c_6341,plain,
    ( r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5496,c_6319])).

tff(c_6344,plain,(
    ~ m1_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6341])).

tff(c_6347,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5967,c_6344])).

tff(c_6352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_89,c_6347])).

tff(c_6353,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6341])).

tff(c_46,plain,(
    ! [C_39,A_33,B_37] :
      ( m2_connsp_2(C_39,A_33,B_37)
      | ~ r1_tarski(B_37,k1_tops_1(A_33,C_39))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6516,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6353,c_46])).

tff(c_6558,plain,(
    m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_291,c_54,c_6516])).

tff(c_6560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_6558])).

tff(c_6562,plain,(
    v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5495])).

tff(c_7253,plain,(
    ! [B_7733,A_7734,C_7735] :
      ( r2_hidden(B_7733,k1_tops_1(A_7734,C_7735))
      | ~ m1_connsp_2(C_7735,A_7734,B_7733)
      | ~ m1_subset_1(C_7735,k1_zfmisc_1(u1_struct_0(A_7734)))
      | ~ m1_subset_1(B_7733,u1_struct_0(A_7734))
      | ~ l1_pre_topc(A_7734)
      | ~ v2_pre_topc(A_7734)
      | v2_struct_0(A_7734) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7274,plain,(
    ! [B_7733] :
      ( r2_hidden(B_7733,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_7733)
      | ~ m1_subset_1(B_7733,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_7253])).

tff(c_7288,plain,(
    ! [B_7733] :
      ( r2_hidden(B_7733,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_7733)
      | ~ m1_subset_1(B_7733,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_7274])).

tff(c_7290,plain,(
    ! [B_7781] :
      ( r2_hidden(B_7781,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_7781)
      | ~ m1_subset_1(B_7781,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_7288])).

tff(c_183,plain,(
    ! [B_83,A_84] :
      ( ~ v1_xboole_0(B_83)
      | ~ r1_tarski(k1_tarski(A_84),B_83) ) ),
    inference(resolution,[status(thm)],[c_80,c_170])).

tff(c_187,plain,(
    ! [B_65,A_64] :
      ( ~ v1_xboole_0(B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_107,c_183])).

tff(c_7314,plain,(
    ! [B_7781] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_7781)
      | ~ m1_subset_1(B_7781,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7290,c_187])).

tff(c_7332,plain,(
    ! [B_7827] :
      ( ~ m1_connsp_2('#skF_5','#skF_3',B_7827)
      | ~ m1_subset_1(B_7827,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6562,c_7314])).

tff(c_7342,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_7332])).

tff(c_7348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_7342])).

tff(c_7350,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_36,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7359,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7350,c_36])).

tff(c_7362,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_7359])).

tff(c_7365,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_7362])).

tff(c_7369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7365])).

tff(c_7371,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_7424,plain,(
    ! [C_7891,B_7892,A_7893] :
      ( ~ v1_xboole_0(C_7891)
      | ~ m1_subset_1(B_7892,k1_zfmisc_1(C_7891))
      | ~ r2_hidden(A_7893,B_7892) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7433,plain,(
    ! [A_7893] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_7893,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_7424])).

tff(c_7434,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7433])).

tff(c_7448,plain,(
    ! [A_7897,B_7898] :
      ( k6_domain_1(A_7897,B_7898) = k1_tarski(B_7898)
      | ~ m1_subset_1(B_7898,A_7897)
      | v1_xboole_0(A_7897) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7460,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_7448])).

tff(c_7466,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_7434,c_7460])).

tff(c_7370,plain,(
    m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_7467,plain,(
    m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7466,c_7370])).

tff(c_7537,plain,(
    ! [A_7918,B_7919] :
      ( m1_subset_1(k6_domain_1(A_7918,B_7919),k1_zfmisc_1(A_7918))
      | ~ m1_subset_1(B_7919,A_7918)
      | v1_xboole_0(A_7918) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7550,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7466,c_7537])).

tff(c_7556,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7550])).

tff(c_7557,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7434,c_7556])).

tff(c_12143,plain,(
    ! [B_12910,A_12911,C_12912] :
      ( r1_tarski(B_12910,k1_tops_1(A_12911,C_12912))
      | ~ m2_connsp_2(C_12912,A_12911,B_12910)
      | ~ m1_subset_1(C_12912,k1_zfmisc_1(u1_struct_0(A_12911)))
      | ~ m1_subset_1(B_12910,k1_zfmisc_1(u1_struct_0(A_12911)))
      | ~ l1_pre_topc(A_12911)
      | ~ v2_pre_topc(A_12911) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12164,plain,(
    ! [B_12910] :
      ( r1_tarski(B_12910,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_12910)
      | ~ m1_subset_1(B_12910,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_12143])).

tff(c_12177,plain,(
    ! [B_12958] :
      ( r1_tarski(B_12958,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_12958)
      | ~ m1_subset_1(B_12958,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_12164])).

tff(c_12187,plain,
    ( r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5'))
    | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7557,c_12177])).

tff(c_12206,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7467,c_12187])).

tff(c_7495,plain,(
    ! [A_7904,C_7905,B_7906] :
      ( m1_subset_1(A_7904,C_7905)
      | ~ m1_subset_1(B_7906,k1_zfmisc_1(C_7905))
      | ~ r2_hidden(A_7904,B_7906) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7519,plain,(
    ! [A_7913,B_7914,A_7915] :
      ( m1_subset_1(A_7913,B_7914)
      | ~ r2_hidden(A_7913,A_7915)
      | ~ r1_tarski(A_7915,B_7914) ) ),
    inference(resolution,[status(thm)],[c_28,c_7495])).

tff(c_7529,plain,(
    ! [A_57,B_7914] :
      ( m1_subset_1(A_57,B_7914)
      | ~ r1_tarski(k1_tarski(A_57),B_7914) ) ),
    inference(resolution,[status(thm)],[c_80,c_7519])).

tff(c_12257,plain,(
    m1_subset_1('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12206,c_7529])).

tff(c_7435,plain,(
    ! [B_7894,A_7895,A_7896] :
      ( ~ v1_xboole_0(B_7894)
      | ~ r2_hidden(A_7895,A_7896)
      | ~ r1_tarski(A_7896,B_7894) ) ),
    inference(resolution,[status(thm)],[c_28,c_7424])).

tff(c_7445,plain,(
    ! [B_7894,A_57] :
      ( ~ v1_xboole_0(B_7894)
      | ~ r1_tarski(k1_tarski(A_57),B_7894) ) ),
    inference(resolution,[status(thm)],[c_80,c_7435])).

tff(c_12258,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12206,c_7445])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12660,plain,(
    ! [C_13692,A_13693,B_13694] :
      ( m1_connsp_2(C_13692,A_13693,B_13694)
      | ~ r2_hidden(B_13694,k1_tops_1(A_13693,C_13692))
      | ~ m1_subset_1(C_13692,k1_zfmisc_1(u1_struct_0(A_13693)))
      | ~ m1_subset_1(B_13694,u1_struct_0(A_13693))
      | ~ l1_pre_topc(A_13693)
      | ~ v2_pre_topc(A_13693)
      | v2_struct_0(A_13693) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_37514,plain,(
    ! [C_25212,A_25213,A_25214] :
      ( m1_connsp_2(C_25212,A_25213,A_25214)
      | ~ m1_subset_1(C_25212,k1_zfmisc_1(u1_struct_0(A_25213)))
      | ~ m1_subset_1(A_25214,u1_struct_0(A_25213))
      | ~ l1_pre_topc(A_25213)
      | ~ v2_pre_topc(A_25213)
      | v2_struct_0(A_25213)
      | v1_xboole_0(k1_tops_1(A_25213,C_25212))
      | ~ m1_subset_1(A_25214,k1_tops_1(A_25213,C_25212)) ) ),
    inference(resolution,[status(thm)],[c_24,c_12660])).

tff(c_37539,plain,(
    ! [A_25214] :
      ( m1_connsp_2('#skF_5','#skF_3',A_25214)
      | ~ m1_subset_1(A_25214,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(A_25214,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_54,c_37514])).

tff(c_37561,plain,(
    ! [A_25214] :
      ( m1_connsp_2('#skF_5','#skF_3',A_25214)
      | ~ m1_subset_1(A_25214,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(A_25214,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_37539])).

tff(c_37563,plain,(
    ! [A_25260] :
      ( m1_connsp_2('#skF_5','#skF_3',A_25260)
      | ~ m1_subset_1(A_25260,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_25260,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12258,c_62,c_37561])).

tff(c_37572,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12257,c_37563])).

tff(c_37578,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_37572])).

tff(c_37580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7371,c_37578])).

tff(c_37582,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7433])).

tff(c_37591,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_37582,c_36])).

tff(c_37594,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_37591])).

tff(c_37597,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_37594])).

tff(c_37601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_37597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.87/6.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.87/6.20  
% 13.87/6.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.87/6.20  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 13.87/6.20  
% 13.87/6.20  %Foreground sorts:
% 13.87/6.20  
% 13.87/6.20  
% 13.87/6.20  %Background operators:
% 13.87/6.20  
% 13.87/6.20  
% 13.87/6.20  %Foreground operators:
% 13.87/6.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.87/6.20  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 13.87/6.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.87/6.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.87/6.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.87/6.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.87/6.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.87/6.20  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 13.87/6.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.87/6.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.87/6.20  tff('#skF_5', type, '#skF_5': $i).
% 13.87/6.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 13.87/6.20  tff('#skF_3', type, '#skF_3': $i).
% 13.87/6.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.87/6.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.87/6.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.87/6.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.87/6.20  tff('#skF_4', type, '#skF_4': $i).
% 13.87/6.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.87/6.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.87/6.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.87/6.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.87/6.20  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 13.87/6.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.87/6.20  
% 14.06/6.23  tff(f_163, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 14.06/6.23  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.06/6.23  tff(f_63, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 14.06/6.23  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 14.06/6.23  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 14.06/6.23  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 14.06/6.23  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 14.06/6.23  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.06/6.23  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.06/6.23  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 14.06/6.23  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 14.06/6.23  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 14.06/6.23  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 14.06/6.23  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 14.06/6.23  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_34, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.06/6.23  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_70, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_89, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 14.06/6.23  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_142, plain, (![C_75, B_76, A_77]: (~v1_xboole_0(C_75) | ~m1_subset_1(B_76, k1_zfmisc_1(C_75)) | ~r2_hidden(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.06/6.23  tff(c_151, plain, (![A_77]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_77, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_142])).
% 14.06/6.23  tff(c_152, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_151])).
% 14.06/6.23  tff(c_153, plain, (![A_78, B_79]: (k6_domain_1(A_78, B_79)=k1_tarski(B_79) | ~m1_subset_1(B_79, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.06/6.23  tff(c_169, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_153])).
% 14.06/6.23  tff(c_188, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_152, c_169])).
% 14.06/6.23  tff(c_64, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_110, plain, (~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64])).
% 14.06/6.23  tff(c_189, plain, (~m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_110])).
% 14.06/6.23  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.06/6.23  tff(c_271, plain, (![A_104, B_105]: (m1_subset_1(k6_domain_1(A_104, B_105), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.06/6.23  tff(c_284, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_271])).
% 14.06/6.23  tff(c_290, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_284])).
% 14.06/6.23  tff(c_291, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_152, c_290])).
% 14.06/6.23  tff(c_5900, plain, (![B_6113, A_6114, C_6115]: (r2_hidden(B_6113, k1_tops_1(A_6114, C_6115)) | ~m1_connsp_2(C_6115, A_6114, B_6113) | ~m1_subset_1(C_6115, k1_zfmisc_1(u1_struct_0(A_6114))) | ~m1_subset_1(B_6113, u1_struct_0(A_6114)) | ~l1_pre_topc(A_6114) | ~v2_pre_topc(A_6114) | v2_struct_0(A_6114))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.06/6.23  tff(c_5921, plain, (![B_6113]: (r2_hidden(B_6113, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_6113) | ~m1_subset_1(B_6113, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_5900])).
% 14.06/6.23  tff(c_5935, plain, (![B_6113]: (r2_hidden(B_6113, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_6113) | ~m1_subset_1(B_6113, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5921])).
% 14.06/6.23  tff(c_5937, plain, (![B_6161]: (r2_hidden(B_6161, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_6161) | ~m1_subset_1(B_6161, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_5935])).
% 14.06/6.23  tff(c_103, plain, (![A_64, B_65]: (m1_subset_1(k1_tarski(A_64), k1_zfmisc_1(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.06/6.23  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.06/6.23  tff(c_107, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_103, c_26])).
% 14.06/6.23  tff(c_74, plain, (![A_57]: (k2_tarski(A_57, A_57)=k1_tarski(A_57))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.06/6.23  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.06/6.23  tff(c_80, plain, (![A_57]: (r2_hidden(A_57, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 14.06/6.23  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.06/6.23  tff(c_215, plain, (![A_90, C_91, B_92]: (m1_subset_1(A_90, C_91) | ~m1_subset_1(B_92, k1_zfmisc_1(C_91)) | ~r2_hidden(A_90, B_92))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.06/6.23  tff(c_236, plain, (![A_97, B_98, A_99]: (m1_subset_1(A_97, B_98) | ~r2_hidden(A_97, A_99) | ~r1_tarski(A_99, B_98))), inference(resolution, [status(thm)], [c_28, c_215])).
% 14.06/6.23  tff(c_249, plain, (![A_100, B_101]: (m1_subset_1(A_100, B_101) | ~r1_tarski(k1_tarski(A_100), B_101))), inference(resolution, [status(thm)], [c_80, c_236])).
% 14.06/6.23  tff(c_253, plain, (![A_64, B_65]: (m1_subset_1(A_64, B_65) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_107, c_249])).
% 14.06/6.23  tff(c_5967, plain, (![B_6161]: (m1_subset_1(B_6161, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_6161) | ~m1_subset_1(B_6161, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5937, c_253])).
% 14.06/6.23  tff(c_5394, plain, (![B_5369, A_5370, C_5371]: (r1_tarski(B_5369, k1_tops_1(A_5370, C_5371)) | ~m2_connsp_2(C_5371, A_5370, B_5369) | ~m1_subset_1(C_5371, k1_zfmisc_1(u1_struct_0(A_5370))) | ~m1_subset_1(B_5369, k1_zfmisc_1(u1_struct_0(A_5370))) | ~l1_pre_topc(A_5370) | ~v2_pre_topc(A_5370))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.06/6.23  tff(c_5415, plain, (![B_5369]: (r1_tarski(B_5369, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_5369) | ~m1_subset_1(B_5369, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_5394])).
% 14.06/6.23  tff(c_5428, plain, (![B_5417]: (r1_tarski(B_5417, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_5417) | ~m1_subset_1(B_5417, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5415])).
% 14.06/6.23  tff(c_5463, plain, (![A_5508]: (r1_tarski(A_5508, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', A_5508) | ~r1_tarski(A_5508, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_28, c_5428])).
% 14.06/6.23  tff(c_170, plain, (![B_80, A_81, A_82]: (~v1_xboole_0(B_80) | ~r2_hidden(A_81, A_82) | ~r1_tarski(A_82, B_80))), inference(resolution, [status(thm)], [c_28, c_142])).
% 14.06/6.23  tff(c_180, plain, (![B_80, A_57]: (~v1_xboole_0(B_80) | ~r1_tarski(k1_tarski(A_57), B_80))), inference(resolution, [status(thm)], [c_80, c_170])).
% 14.06/6.23  tff(c_5495, plain, (![A_57]: (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_57)) | ~r1_tarski(k1_tarski(A_57), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5463, c_180])).
% 14.06/6.23  tff(c_5496, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_5495])).
% 14.06/6.23  tff(c_5971, plain, (![B_6207]: (m1_subset_1(B_6207, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_6207) | ~m1_subset_1(B_6207, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5937, c_253])).
% 14.06/6.23  tff(c_40, plain, (![A_24, B_25]: (k6_domain_1(A_24, B_25)=k1_tarski(B_25) | ~m1_subset_1(B_25, A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.06/6.23  tff(c_5976, plain, (![B_6207]: (k6_domain_1(k1_tops_1('#skF_3', '#skF_5'), B_6207)=k1_tarski(B_6207) | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_6207) | ~m1_subset_1(B_6207, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5971, c_40])).
% 14.06/6.23  tff(c_6286, plain, (![B_6669]: (k6_domain_1(k1_tops_1('#skF_3', '#skF_5'), B_6669)=k1_tarski(B_6669) | ~m1_connsp_2('#skF_5', '#skF_3', B_6669) | ~m1_subset_1(B_6669, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_5496, c_5976])).
% 14.06/6.23  tff(c_6307, plain, (k6_domain_1(k1_tops_1('#skF_3', '#skF_5'), '#skF_4')=k1_tarski('#skF_4') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_6286])).
% 14.06/6.23  tff(c_6312, plain, (k6_domain_1(k1_tops_1('#skF_3', '#skF_5'), '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_6307])).
% 14.06/6.23  tff(c_288, plain, (![A_104, B_105]: (r1_tarski(k6_domain_1(A_104, B_105), A_104) | ~m1_subset_1(B_105, A_104) | v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_271, c_26])).
% 14.06/6.23  tff(c_6319, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6312, c_288])).
% 14.06/6.23  tff(c_6341, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_5496, c_6319])).
% 14.06/6.23  tff(c_6344, plain, (~m1_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6341])).
% 14.06/6.23  tff(c_6347, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_5967, c_6344])).
% 14.06/6.23  tff(c_6352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_89, c_6347])).
% 14.06/6.23  tff(c_6353, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_6341])).
% 14.06/6.23  tff(c_46, plain, (![C_39, A_33, B_37]: (m2_connsp_2(C_39, A_33, B_37) | ~r1_tarski(B_37, k1_tops_1(A_33, C_39)) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.06/6.23  tff(c_6516, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6353, c_46])).
% 14.06/6.23  tff(c_6558, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_291, c_54, c_6516])).
% 14.06/6.23  tff(c_6560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_6558])).
% 14.06/6.23  tff(c_6562, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_5495])).
% 14.06/6.23  tff(c_7253, plain, (![B_7733, A_7734, C_7735]: (r2_hidden(B_7733, k1_tops_1(A_7734, C_7735)) | ~m1_connsp_2(C_7735, A_7734, B_7733) | ~m1_subset_1(C_7735, k1_zfmisc_1(u1_struct_0(A_7734))) | ~m1_subset_1(B_7733, u1_struct_0(A_7734)) | ~l1_pre_topc(A_7734) | ~v2_pre_topc(A_7734) | v2_struct_0(A_7734))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.06/6.23  tff(c_7274, plain, (![B_7733]: (r2_hidden(B_7733, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_7733) | ~m1_subset_1(B_7733, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_7253])).
% 14.06/6.23  tff(c_7288, plain, (![B_7733]: (r2_hidden(B_7733, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_7733) | ~m1_subset_1(B_7733, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_7274])).
% 14.06/6.23  tff(c_7290, plain, (![B_7781]: (r2_hidden(B_7781, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_7781) | ~m1_subset_1(B_7781, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_7288])).
% 14.06/6.23  tff(c_183, plain, (![B_83, A_84]: (~v1_xboole_0(B_83) | ~r1_tarski(k1_tarski(A_84), B_83))), inference(resolution, [status(thm)], [c_80, c_170])).
% 14.06/6.23  tff(c_187, plain, (![B_65, A_64]: (~v1_xboole_0(B_65) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_107, c_183])).
% 14.06/6.23  tff(c_7314, plain, (![B_7781]: (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_7781) | ~m1_subset_1(B_7781, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7290, c_187])).
% 14.06/6.23  tff(c_7332, plain, (![B_7827]: (~m1_connsp_2('#skF_5', '#skF_3', B_7827) | ~m1_subset_1(B_7827, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6562, c_7314])).
% 14.06/6.23  tff(c_7342, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_7332])).
% 14.06/6.23  tff(c_7348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_7342])).
% 14.06/6.23  tff(c_7350, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_151])).
% 14.06/6.23  tff(c_36, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.06/6.23  tff(c_7359, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_7350, c_36])).
% 14.06/6.23  tff(c_7362, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_7359])).
% 14.06/6.23  tff(c_7365, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_7362])).
% 14.06/6.23  tff(c_7369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_7365])).
% 14.06/6.23  tff(c_7371, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 14.06/6.23  tff(c_7424, plain, (![C_7891, B_7892, A_7893]: (~v1_xboole_0(C_7891) | ~m1_subset_1(B_7892, k1_zfmisc_1(C_7891)) | ~r2_hidden(A_7893, B_7892))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.06/6.23  tff(c_7433, plain, (![A_7893]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_7893, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_7424])).
% 14.06/6.23  tff(c_7434, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_7433])).
% 14.06/6.23  tff(c_7448, plain, (![A_7897, B_7898]: (k6_domain_1(A_7897, B_7898)=k1_tarski(B_7898) | ~m1_subset_1(B_7898, A_7897) | v1_xboole_0(A_7897))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.06/6.23  tff(c_7460, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_7448])).
% 14.06/6.23  tff(c_7466, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_7434, c_7460])).
% 14.06/6.23  tff(c_7370, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 14.06/6.23  tff(c_7467, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7466, c_7370])).
% 14.06/6.23  tff(c_7537, plain, (![A_7918, B_7919]: (m1_subset_1(k6_domain_1(A_7918, B_7919), k1_zfmisc_1(A_7918)) | ~m1_subset_1(B_7919, A_7918) | v1_xboole_0(A_7918))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.06/6.23  tff(c_7550, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7466, c_7537])).
% 14.06/6.23  tff(c_7556, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_7550])).
% 14.06/6.23  tff(c_7557, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_7434, c_7556])).
% 14.06/6.23  tff(c_12143, plain, (![B_12910, A_12911, C_12912]: (r1_tarski(B_12910, k1_tops_1(A_12911, C_12912)) | ~m2_connsp_2(C_12912, A_12911, B_12910) | ~m1_subset_1(C_12912, k1_zfmisc_1(u1_struct_0(A_12911))) | ~m1_subset_1(B_12910, k1_zfmisc_1(u1_struct_0(A_12911))) | ~l1_pre_topc(A_12911) | ~v2_pre_topc(A_12911))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.06/6.23  tff(c_12164, plain, (![B_12910]: (r1_tarski(B_12910, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_12910) | ~m1_subset_1(B_12910, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_12143])).
% 14.06/6.23  tff(c_12177, plain, (![B_12958]: (r1_tarski(B_12958, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_12958) | ~m1_subset_1(B_12958, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_12164])).
% 14.06/6.23  tff(c_12187, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_7557, c_12177])).
% 14.06/6.23  tff(c_12206, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7467, c_12187])).
% 14.06/6.23  tff(c_7495, plain, (![A_7904, C_7905, B_7906]: (m1_subset_1(A_7904, C_7905) | ~m1_subset_1(B_7906, k1_zfmisc_1(C_7905)) | ~r2_hidden(A_7904, B_7906))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.06/6.23  tff(c_7519, plain, (![A_7913, B_7914, A_7915]: (m1_subset_1(A_7913, B_7914) | ~r2_hidden(A_7913, A_7915) | ~r1_tarski(A_7915, B_7914))), inference(resolution, [status(thm)], [c_28, c_7495])).
% 14.06/6.23  tff(c_7529, plain, (![A_57, B_7914]: (m1_subset_1(A_57, B_7914) | ~r1_tarski(k1_tarski(A_57), B_7914))), inference(resolution, [status(thm)], [c_80, c_7519])).
% 14.06/6.23  tff(c_12257, plain, (m1_subset_1('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_12206, c_7529])).
% 14.06/6.23  tff(c_7435, plain, (![B_7894, A_7895, A_7896]: (~v1_xboole_0(B_7894) | ~r2_hidden(A_7895, A_7896) | ~r1_tarski(A_7896, B_7894))), inference(resolution, [status(thm)], [c_28, c_7424])).
% 14.06/6.23  tff(c_7445, plain, (![B_7894, A_57]: (~v1_xboole_0(B_7894) | ~r1_tarski(k1_tarski(A_57), B_7894))), inference(resolution, [status(thm)], [c_80, c_7435])).
% 14.06/6.23  tff(c_12258, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_12206, c_7445])).
% 14.06/6.23  tff(c_24, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.06/6.23  tff(c_12660, plain, (![C_13692, A_13693, B_13694]: (m1_connsp_2(C_13692, A_13693, B_13694) | ~r2_hidden(B_13694, k1_tops_1(A_13693, C_13692)) | ~m1_subset_1(C_13692, k1_zfmisc_1(u1_struct_0(A_13693))) | ~m1_subset_1(B_13694, u1_struct_0(A_13693)) | ~l1_pre_topc(A_13693) | ~v2_pre_topc(A_13693) | v2_struct_0(A_13693))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.06/6.23  tff(c_37514, plain, (![C_25212, A_25213, A_25214]: (m1_connsp_2(C_25212, A_25213, A_25214) | ~m1_subset_1(C_25212, k1_zfmisc_1(u1_struct_0(A_25213))) | ~m1_subset_1(A_25214, u1_struct_0(A_25213)) | ~l1_pre_topc(A_25213) | ~v2_pre_topc(A_25213) | v2_struct_0(A_25213) | v1_xboole_0(k1_tops_1(A_25213, C_25212)) | ~m1_subset_1(A_25214, k1_tops_1(A_25213, C_25212)))), inference(resolution, [status(thm)], [c_24, c_12660])).
% 14.06/6.23  tff(c_37539, plain, (![A_25214]: (m1_connsp_2('#skF_5', '#skF_3', A_25214) | ~m1_subset_1(A_25214, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(A_25214, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_54, c_37514])).
% 14.06/6.23  tff(c_37561, plain, (![A_25214]: (m1_connsp_2('#skF_5', '#skF_3', A_25214) | ~m1_subset_1(A_25214, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(A_25214, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_37539])).
% 14.06/6.23  tff(c_37563, plain, (![A_25260]: (m1_connsp_2('#skF_5', '#skF_3', A_25260) | ~m1_subset_1(A_25260, u1_struct_0('#skF_3')) | ~m1_subset_1(A_25260, k1_tops_1('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_12258, c_62, c_37561])).
% 14.06/6.23  tff(c_37572, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12257, c_37563])).
% 14.06/6.23  tff(c_37578, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_37572])).
% 14.06/6.23  tff(c_37580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7371, c_37578])).
% 14.06/6.23  tff(c_37582, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_7433])).
% 14.06/6.23  tff(c_37591, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_37582, c_36])).
% 14.06/6.23  tff(c_37594, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_37591])).
% 14.06/6.23  tff(c_37597, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_37594])).
% 14.06/6.23  tff(c_37601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_37597])).
% 14.06/6.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.06/6.23  
% 14.06/6.23  Inference rules
% 14.06/6.23  ----------------------
% 14.06/6.23  #Ref     : 0
% 14.06/6.23  #Sup     : 6432
% 14.06/6.23  #Fact    : 52
% 14.06/6.23  #Define  : 0
% 14.06/6.23  #Split   : 40
% 14.06/6.23  #Chain   : 0
% 14.06/6.23  #Close   : 0
% 14.06/6.23  
% 14.06/6.23  Ordering : KBO
% 14.06/6.23  
% 14.06/6.23  Simplification rules
% 14.06/6.23  ----------------------
% 14.06/6.23  #Subsume      : 1928
% 14.06/6.23  #Demod        : 1217
% 14.06/6.23  #Tautology    : 1792
% 14.06/6.23  #SimpNegUnit  : 627
% 14.06/6.23  #BackRed      : 2
% 14.06/6.23  
% 14.06/6.23  #Partial instantiations: 17820
% 14.06/6.23  #Strategies tried      : 1
% 14.06/6.23  
% 14.06/6.23  Timing (in seconds)
% 14.06/6.23  ----------------------
% 14.06/6.23  Preprocessing        : 0.37
% 14.06/6.23  Parsing              : 0.19
% 14.06/6.23  CNF conversion       : 0.03
% 14.06/6.23  Main loop            : 5.07
% 14.06/6.23  Inferencing          : 1.75
% 14.06/6.23  Reduction            : 1.32
% 14.06/6.23  Demodulation         : 0.91
% 14.06/6.23  BG Simplification    : 0.16
% 14.06/6.23  Subsumption          : 1.53
% 14.06/6.23  Abstraction          : 0.24
% 14.06/6.23  MUC search           : 0.00
% 14.06/6.23  Cooper               : 0.00
% 14.06/6.23  Total                : 5.49
% 14.06/6.23  Index Insertion      : 0.00
% 14.06/6.23  Index Deletion       : 0.00
% 14.06/6.23  Index Matching       : 0.00
% 14.06/6.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
