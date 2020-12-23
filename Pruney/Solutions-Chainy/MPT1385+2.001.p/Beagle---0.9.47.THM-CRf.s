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
% DateTime   : Thu Dec  3 10:24:15 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 286 expanded)
%              Number of leaves         :   34 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  285 ( 897 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_75,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_89,axiom,(
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

tff(f_143,axiom,(
    ! [A] :
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_73,plain,(
    ! [B_59,A_60] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_78,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_79,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_89,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_85])).

tff(c_44,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_67,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_90,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_67])).

tff(c_50,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_95,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4'))
    | m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_50])).

tff(c_96,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_95])).

tff(c_288,plain,(
    ! [B_99,A_100,C_101] :
      ( r2_hidden(B_99,k1_tops_1(A_100,C_101))
      | ~ m1_connsp_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_99,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_297,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_288])).

tff(c_306,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_297])).

tff(c_307,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_306])).

tff(c_98,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k6_domain_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_98])).

tff(c_111,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_107])).

tff(c_112,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_111])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_262,plain,(
    ! [C_95,A_96,B_97] :
      ( m2_connsp_2(C_95,A_96,B_97)
      | ~ r1_tarski(B_97,k1_tops_1(A_96,C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_337,plain,(
    ! [C_107,A_108,A_109] :
      ( m2_connsp_2(C_107,A_108,k1_tarski(A_109))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(k1_tarski(A_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | ~ r2_hidden(A_109,k1_tops_1(A_108,C_107)) ) ),
    inference(resolution,[status(thm)],[c_10,c_262])).

tff(c_346,plain,(
    ! [A_109] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_109))
      | ~ m1_subset_1(k1_tarski(A_109),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r2_hidden(A_109,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_34,c_337])).

tff(c_355,plain,(
    ! [A_110] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_110))
      | ~ m1_subset_1(k1_tarski(A_110),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_110,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_346])).

tff(c_358,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_112,c_355])).

tff(c_361,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_358])).

tff(c_364,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_307,c_361])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_96,c_364])).

tff(c_369,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_371,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_50])).

tff(c_422,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ m1_connsp_2(B_126,A_127,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_127))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_426,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_371,c_422])).

tff(c_430,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_36,c_426])).

tff(c_431,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_430])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_434,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_431,c_2])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_434])).

tff(c_439,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_446,plain,(
    ! [B_130,A_131] :
      ( v1_xboole_0(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_450,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_446])).

tff(c_460,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_451,plain,(
    ! [A_132,B_133] :
      ( k6_domain_1(A_132,B_133) = k1_tarski(B_133)
      | ~ m1_subset_1(B_133,A_132)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_459,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_451])).

tff(c_461,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_459])).

tff(c_467,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4'))
    | m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_50])).

tff(c_468,plain,(
    m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_467])).

tff(c_470,plain,(
    ! [A_134,B_135] :
      ( m1_subset_1(k6_domain_1(A_134,B_135),k1_zfmisc_1(A_134))
      | ~ m1_subset_1(B_135,A_134)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_479,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_470])).

tff(c_483,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_479])).

tff(c_484,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_483])).

tff(c_573,plain,(
    ! [B_162,A_163,C_164] :
      ( r1_tarski(B_162,k1_tops_1(A_163,C_164))
      | ~ m2_connsp_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_582,plain,(
    ! [B_162] :
      ( r1_tarski(B_162,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_573])).

tff(c_591,plain,(
    ! [B_165] :
      ( r1_tarski(B_165,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_582])).

tff(c_598,plain,
    ( r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5'))
    | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_484,c_591])).

tff(c_612,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_598])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_625,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_612,c_8])).

tff(c_685,plain,(
    ! [C_174,A_175,B_176] :
      ( m1_connsp_2(C_174,A_175,B_176)
      | ~ r2_hidden(B_176,k1_tops_1(A_175,C_174))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_691,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_625,c_685])).

tff(c_705,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_691])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_439,c_705])).

tff(c_709,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_30,plain,(
    ! [A_37,B_38] :
      ( m1_connsp_2('#skF_2'(A_37,B_38),A_37,B_38)
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_730,plain,(
    ! [C_184,A_185,B_186] :
      ( m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_connsp_2(C_184,A_185,B_186)
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_734,plain,(
    ! [A_187,B_188] :
      ( m1_subset_1('#skF_2'(A_187,B_188),k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_30,c_730])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_743,plain,(
    ! [A_189,B_190] :
      ( v1_xboole_0('#skF_2'(A_189,B_190))
      | ~ v1_xboole_0(u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_734,c_12])).

tff(c_746,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_743])).

tff(c_749,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_709,c_746])).

tff(c_750,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_749])).

tff(c_733,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1('#skF_2'(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_30,c_730])).

tff(c_751,plain,(
    ! [C_191,B_192,A_193] :
      ( r2_hidden(C_191,B_192)
      | ~ m1_connsp_2(B_192,A_193,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_193))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_773,plain,(
    ! [B_196,A_197] :
      ( r2_hidden(B_196,'#skF_2'(A_197,B_196))
      | ~ m1_subset_1('#skF_2'(A_197,B_196),k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_subset_1(B_196,u1_struct_0(A_197))
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_30,c_751])).

tff(c_777,plain,(
    ! [B_198,A_199] :
      ( r2_hidden(B_198,'#skF_2'(A_199,B_198))
      | ~ m1_subset_1(B_198,u1_struct_0(A_199))
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_733,c_773])).

tff(c_782,plain,(
    ! [A_200,B_201] :
      ( ~ v1_xboole_0('#skF_2'(A_200,B_201))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_777,c_2])).

tff(c_785,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_782])).

tff(c_788,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_750,c_785])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 19:54:30 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  
% 3.24/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.24/1.47  
% 3.24/1.47  %Foreground sorts:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Background operators:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Foreground operators:
% 3.24/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.24/1.47  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.24/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.24/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.47  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.24/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.47  
% 3.24/1.49  tff(f_161, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.24/1.49  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.24/1.49  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.24/1.49  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.24/1.49  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.24/1.49  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.24/1.49  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.24/1.49  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.24/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.24/1.49  tff(f_126, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.24/1.49  tff(f_103, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.24/1.49  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_73, plain, (![B_59, A_60]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.49  tff(c_77, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_73])).
% 3.24/1.49  tff(c_78, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_77])).
% 3.24/1.49  tff(c_79, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.49  tff(c_85, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_79])).
% 3.24/1.49  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_85])).
% 3.24/1.49  tff(c_44, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_67, plain, (~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.24/1.49  tff(c_90, plain, (~m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_67])).
% 3.24/1.49  tff(c_50, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.49  tff(c_95, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4')) | m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_50])).
% 3.24/1.49  tff(c_96, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_90, c_95])).
% 3.24/1.49  tff(c_288, plain, (![B_99, A_100, C_101]: (r2_hidden(B_99, k1_tops_1(A_100, C_101)) | ~m1_connsp_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_99, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.49  tff(c_297, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_288])).
% 3.24/1.49  tff(c_306, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_297])).
% 3.24/1.49  tff(c_307, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_306])).
% 3.24/1.49  tff(c_98, plain, (![A_63, B_64]: (m1_subset_1(k6_domain_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.49  tff(c_107, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_98])).
% 3.24/1.49  tff(c_111, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_107])).
% 3.24/1.49  tff(c_112, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_78, c_111])).
% 3.24/1.49  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.49  tff(c_262, plain, (![C_95, A_96, B_97]: (m2_connsp_2(C_95, A_96, B_97) | ~r1_tarski(B_97, k1_tops_1(A_96, C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.24/1.49  tff(c_337, plain, (![C_107, A_108, A_109]: (m2_connsp_2(C_107, A_108, k1_tarski(A_109)) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(k1_tarski(A_109), k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | ~r2_hidden(A_109, k1_tops_1(A_108, C_107)))), inference(resolution, [status(thm)], [c_10, c_262])).
% 3.24/1.49  tff(c_346, plain, (![A_109]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_109)) | ~m1_subset_1(k1_tarski(A_109), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden(A_109, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_34, c_337])).
% 3.24/1.49  tff(c_355, plain, (![A_110]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_110)) | ~m1_subset_1(k1_tarski(A_110), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_110, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_346])).
% 3.24/1.49  tff(c_358, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_112, c_355])).
% 3.24/1.49  tff(c_361, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_90, c_358])).
% 3.24/1.49  tff(c_364, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_307, c_361])).
% 3.24/1.49  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_96, c_364])).
% 3.24/1.49  tff(c_369, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_77])).
% 3.24/1.49  tff(c_371, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_67, c_50])).
% 3.24/1.49  tff(c_422, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~m1_connsp_2(B_126, A_127, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_127)) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.24/1.49  tff(c_426, plain, (r2_hidden('#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_371, c_422])).
% 3.24/1.49  tff(c_430, plain, (r2_hidden('#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_36, c_426])).
% 3.24/1.49  tff(c_431, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_430])).
% 3.24/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.49  tff(c_434, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_431, c_2])).
% 3.24/1.49  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_434])).
% 3.24/1.49  tff(c_439, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 3.24/1.49  tff(c_446, plain, (![B_130, A_131]: (v1_xboole_0(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.49  tff(c_450, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_446])).
% 3.24/1.49  tff(c_460, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_450])).
% 3.24/1.49  tff(c_451, plain, (![A_132, B_133]: (k6_domain_1(A_132, B_133)=k1_tarski(B_133) | ~m1_subset_1(B_133, A_132) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.49  tff(c_459, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_451])).
% 3.24/1.49  tff(c_461, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_460, c_459])).
% 3.24/1.49  tff(c_467, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4')) | m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_50])).
% 3.24/1.49  tff(c_468, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_439, c_467])).
% 3.24/1.49  tff(c_470, plain, (![A_134, B_135]: (m1_subset_1(k6_domain_1(A_134, B_135), k1_zfmisc_1(A_134)) | ~m1_subset_1(B_135, A_134) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.49  tff(c_479, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_461, c_470])).
% 3.24/1.49  tff(c_483, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_479])).
% 3.24/1.49  tff(c_484, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_460, c_483])).
% 3.24/1.49  tff(c_573, plain, (![B_162, A_163, C_164]: (r1_tarski(B_162, k1_tops_1(A_163, C_164)) | ~m2_connsp_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.24/1.49  tff(c_582, plain, (![B_162]: (r1_tarski(B_162, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_573])).
% 3.24/1.49  tff(c_591, plain, (![B_165]: (r1_tarski(B_165, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_582])).
% 3.24/1.49  tff(c_598, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_484, c_591])).
% 3.24/1.49  tff(c_612, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_598])).
% 3.24/1.49  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.49  tff(c_625, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_612, c_8])).
% 3.24/1.49  tff(c_685, plain, (![C_174, A_175, B_176]: (m1_connsp_2(C_174, A_175, B_176) | ~r2_hidden(B_176, k1_tops_1(A_175, C_174)) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.49  tff(c_691, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_625, c_685])).
% 3.24/1.49  tff(c_705, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_691])).
% 3.24/1.49  tff(c_707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_439, c_705])).
% 3.24/1.49  tff(c_709, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_450])).
% 3.24/1.49  tff(c_30, plain, (![A_37, B_38]: (m1_connsp_2('#skF_2'(A_37, B_38), A_37, B_38) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.24/1.49  tff(c_730, plain, (![C_184, A_185, B_186]: (m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(A_185))) | ~m1_connsp_2(C_184, A_185, B_186) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.24/1.49  tff(c_734, plain, (![A_187, B_188]: (m1_subset_1('#skF_2'(A_187, B_188), k1_zfmisc_1(u1_struct_0(A_187))) | ~m1_subset_1(B_188, u1_struct_0(A_187)) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(resolution, [status(thm)], [c_30, c_730])).
% 3.24/1.49  tff(c_12, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.49  tff(c_743, plain, (![A_189, B_190]: (v1_xboole_0('#skF_2'(A_189, B_190)) | ~v1_xboole_0(u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_734, c_12])).
% 3.24/1.49  tff(c_746, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_743])).
% 3.24/1.49  tff(c_749, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_709, c_746])).
% 3.24/1.49  tff(c_750, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_749])).
% 3.24/1.49  tff(c_733, plain, (![A_37, B_38]: (m1_subset_1('#skF_2'(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(resolution, [status(thm)], [c_30, c_730])).
% 3.24/1.49  tff(c_751, plain, (![C_191, B_192, A_193]: (r2_hidden(C_191, B_192) | ~m1_connsp_2(B_192, A_193, C_191) | ~m1_subset_1(C_191, u1_struct_0(A_193)) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.24/1.49  tff(c_773, plain, (![B_196, A_197]: (r2_hidden(B_196, '#skF_2'(A_197, B_196)) | ~m1_subset_1('#skF_2'(A_197, B_196), k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_subset_1(B_196, u1_struct_0(A_197)) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(resolution, [status(thm)], [c_30, c_751])).
% 3.24/1.49  tff(c_777, plain, (![B_198, A_199]: (r2_hidden(B_198, '#skF_2'(A_199, B_198)) | ~m1_subset_1(B_198, u1_struct_0(A_199)) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_733, c_773])).
% 3.24/1.49  tff(c_782, plain, (![A_200, B_201]: (~v1_xboole_0('#skF_2'(A_200, B_201)) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(resolution, [status(thm)], [c_777, c_2])).
% 3.24/1.49  tff(c_785, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_782])).
% 3.24/1.49  tff(c_788, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_750, c_785])).
% 3.24/1.49  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_788])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 143
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 14
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Subsume      : 10
% 3.24/1.49  #Demod        : 121
% 3.24/1.49  #Tautology    : 45
% 3.24/1.49  #SimpNegUnit  : 34
% 3.24/1.49  #BackRed      : 2
% 3.24/1.49  
% 3.24/1.49  #Partial instantiations: 0
% 3.24/1.49  #Strategies tried      : 1
% 3.24/1.49  
% 3.24/1.49  Timing (in seconds)
% 3.24/1.49  ----------------------
% 3.24/1.50  Preprocessing        : 0.33
% 3.24/1.50  Parsing              : 0.18
% 3.24/1.50  CNF conversion       : 0.02
% 3.24/1.50  Main loop            : 0.38
% 3.24/1.50  Inferencing          : 0.15
% 3.24/1.50  Reduction            : 0.11
% 3.24/1.50  Demodulation         : 0.07
% 3.24/1.50  BG Simplification    : 0.02
% 3.24/1.50  Subsumption          : 0.06
% 3.24/1.50  Abstraction          : 0.02
% 3.24/1.50  MUC search           : 0.00
% 3.24/1.50  Cooper               : 0.00
% 3.24/1.50  Total                : 0.75
% 3.24/1.50  Index Insertion      : 0.00
% 3.24/1.50  Index Deletion       : 0.00
% 3.24/1.50  Index Matching       : 0.00
% 3.24/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
