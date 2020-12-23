%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 244 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  248 ( 757 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_142,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
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

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_124,axiom,(
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

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_49,plain,(
    ! [C_46,B_47,A_48] :
      ( ~ v1_xboole_0(C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_53,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_55,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_65,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_61])).

tff(c_36,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_66,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54])).

tff(c_42,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_92,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_42])).

tff(c_93,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_92])).

tff(c_250,plain,(
    ! [B_88,A_89,C_90] :
      ( r2_hidden(B_88,k1_tops_1(A_89,C_90))
      | ~ m1_connsp_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_88,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_259,plain,(
    ! [B_88] :
      ( r2_hidden(B_88,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_250])).

tff(c_268,plain,(
    ! [B_88] :
      ( r2_hidden(B_88,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_259])).

tff(c_269,plain,(
    ! [B_88] :
      ( r2_hidden(B_88,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_268])).

tff(c_71,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_71])).

tff(c_83,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_79])).

tff(c_84,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_83])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [C_70,A_71,B_72] :
      ( m2_connsp_2(C_70,A_71,B_72)
      | ~ r1_tarski(B_72,k1_tops_1(A_71,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_277,plain,(
    ! [C_92,A_93,A_94] :
      ( m2_connsp_2(C_92,A_93,k1_tarski(A_94))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(k1_tarski(A_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | ~ r2_hidden(A_94,k1_tops_1(A_93,C_92)) ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_286,plain,(
    ! [A_94] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_94))
      | ~ m1_subset_1(k1_tarski(A_94),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r2_hidden(A_94,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_26,c_277])).

tff(c_302,plain,(
    ! [A_96] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_96))
      | ~ m1_subset_1(k1_tarski(A_96),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_96,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_286])).

tff(c_305,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_302])).

tff(c_308,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_305])).

tff(c_311,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_269,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_93,c_311])).

tff(c_316,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_323,plain,(
    ! [A_97,B_98] :
      ( k6_domain_1(A_97,B_98) = k1_tarski(B_98)
      | ~ m1_subset_1(B_98,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_329,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_323])).

tff(c_333,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_329])).

tff(c_318,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_318])).

tff(c_320,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_335,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_320])).

tff(c_340,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k6_domain_1(A_99,B_100),k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,A_99)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_348,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_340])).

tff(c_352,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_348])).

tff(c_353,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_352])).

tff(c_421,plain,(
    ! [B_122,A_123,C_124] :
      ( r1_tarski(B_122,k1_tops_1(A_123,C_124))
      | ~ m2_connsp_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_430,plain,(
    ! [B_122] :
      ( r1_tarski(B_122,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_421])).

tff(c_444,plain,(
    ! [B_128] :
      ( r1_tarski(B_128,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_430])).

tff(c_451,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4'))
    | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_353,c_444])).

tff(c_465,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_451])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | ~ r1_tarski(k1_tarski(A_1),B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_478,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_465,c_2])).

tff(c_503,plain,(
    ! [C_132,A_133,B_134] :
      ( m1_connsp_2(C_132,A_133,B_134)
      | ~ r2_hidden(B_134,k1_tops_1(A_133,C_132))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_505,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_478,c_503])).

tff(c_508,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_505])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_316,c_508])).

tff(c_512,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_22,plain,(
    ! [A_28,B_29] :
      ( m1_connsp_2('#skF_1'(A_28,B_29),A_28,B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_615,plain,(
    ! [C_158,A_159,B_160] :
      ( m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_connsp_2(C_158,A_159,B_160)
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_618,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1('#skF_1'(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_615])).

tff(c_619,plain,(
    ! [C_161,B_162,A_163] :
      ( r2_hidden(C_161,B_162)
      | ~ m1_connsp_2(B_162,A_163,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_163))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_632,plain,(
    ! [B_169,A_170] :
      ( r2_hidden(B_169,'#skF_1'(A_170,B_169))
      | ~ m1_subset_1('#skF_1'(A_170,B_169),k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(B_169,u1_struct_0(A_170))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_22,c_619])).

tff(c_636,plain,(
    ! [B_171,A_172] :
      ( r2_hidden(B_171,'#skF_1'(A_172,B_171))
      | ~ m1_subset_1(B_171,u1_struct_0(A_172))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_618,c_632])).

tff(c_623,plain,(
    ! [A_164,B_165] :
      ( m1_subset_1('#skF_1'(A_164,B_165),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_22,c_615])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_630,plain,(
    ! [A_164,A_3,B_165] :
      ( ~ v1_xboole_0(u1_struct_0(A_164))
      | ~ r2_hidden(A_3,'#skF_1'(A_164,B_165))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_623,c_6])).

tff(c_641,plain,(
    ! [A_173,B_174] :
      ( ~ v1_xboole_0(u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_636,c_630])).

tff(c_644,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_641])).

tff(c_647,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_512,c_644])).

tff(c_649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.46  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.00/1.46  
% 3.00/1.46  %Foreground sorts:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Background operators:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Foreground operators:
% 3.00/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.46  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.00/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.00/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.00/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.00/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.46  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.00/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.46  
% 3.02/1.48  tff(f_142, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.02/1.48  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.02/1.48  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.02/1.48  tff(f_67, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.02/1.48  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.02/1.48  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.02/1.48  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.02/1.48  tff(f_107, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.02/1.48  tff(f_95, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.02/1.48  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.02/1.48  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_49, plain, (![C_46, B_47, A_48]: (~v1_xboole_0(C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.48  tff(c_52, plain, (![A_48]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_49])).
% 3.02/1.48  tff(c_53, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.02/1.48  tff(c_55, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.48  tff(c_61, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_55])).
% 3.02/1.48  tff(c_65, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_61])).
% 3.02/1.48  tff(c_36, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_54, plain, (~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.02/1.48  tff(c_66, plain, (~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54])).
% 3.02/1.48  tff(c_42, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.48  tff(c_92, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_42])).
% 3.02/1.48  tff(c_93, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_92])).
% 3.02/1.48  tff(c_250, plain, (![B_88, A_89, C_90]: (r2_hidden(B_88, k1_tops_1(A_89, C_90)) | ~m1_connsp_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_88, u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.48  tff(c_259, plain, (![B_88]: (r2_hidden(B_88, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_250])).
% 3.02/1.48  tff(c_268, plain, (![B_88]: (r2_hidden(B_88, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_259])).
% 3.02/1.48  tff(c_269, plain, (![B_88]: (r2_hidden(B_88, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_268])).
% 3.02/1.48  tff(c_71, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.48  tff(c_79, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_71])).
% 3.02/1.48  tff(c_83, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_79])).
% 3.02/1.48  tff(c_84, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_53, c_83])).
% 3.02/1.48  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.48  tff(c_154, plain, (![C_70, A_71, B_72]: (m2_connsp_2(C_70, A_71, B_72) | ~r1_tarski(B_72, k1_tops_1(A_71, C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.48  tff(c_277, plain, (![C_92, A_93, A_94]: (m2_connsp_2(C_92, A_93, k1_tarski(A_94)) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(k1_tarski(A_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | ~r2_hidden(A_94, k1_tops_1(A_93, C_92)))), inference(resolution, [status(thm)], [c_4, c_154])).
% 3.02/1.48  tff(c_286, plain, (![A_94]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_94)) | ~m1_subset_1(k1_tarski(A_94), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden(A_94, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_26, c_277])).
% 3.02/1.48  tff(c_302, plain, (![A_96]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_96)) | ~m1_subset_1(k1_tarski(A_96), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_96, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_286])).
% 3.02/1.48  tff(c_305, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_302])).
% 3.02/1.48  tff(c_308, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_305])).
% 3.02/1.48  tff(c_311, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_269, c_308])).
% 3.02/1.48  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_93, c_311])).
% 3.02/1.48  tff(c_316, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.02/1.48  tff(c_323, plain, (![A_97, B_98]: (k6_domain_1(A_97, B_98)=k1_tarski(B_98) | ~m1_subset_1(B_98, A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.48  tff(c_329, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_323])).
% 3.02/1.48  tff(c_333, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_329])).
% 3.02/1.48  tff(c_318, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.02/1.48  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_318])).
% 3.02/1.48  tff(c_320, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 3.02/1.48  tff(c_335, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_320])).
% 3.02/1.48  tff(c_340, plain, (![A_99, B_100]: (m1_subset_1(k6_domain_1(A_99, B_100), k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, A_99) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.48  tff(c_348, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_340])).
% 3.02/1.48  tff(c_352, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_348])).
% 3.02/1.48  tff(c_353, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_53, c_352])).
% 3.02/1.48  tff(c_421, plain, (![B_122, A_123, C_124]: (r1_tarski(B_122, k1_tops_1(A_123, C_124)) | ~m2_connsp_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.48  tff(c_430, plain, (![B_122]: (r1_tarski(B_122, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_421])).
% 3.02/1.48  tff(c_444, plain, (![B_128]: (r1_tarski(B_128, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_430])).
% 3.02/1.48  tff(c_451, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_353, c_444])).
% 3.02/1.48  tff(c_465, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_451])).
% 3.02/1.48  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | ~r1_tarski(k1_tarski(A_1), B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.48  tff(c_478, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_465, c_2])).
% 3.02/1.48  tff(c_503, plain, (![C_132, A_133, B_134]: (m1_connsp_2(C_132, A_133, B_134) | ~r2_hidden(B_134, k1_tops_1(A_133, C_132)) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.48  tff(c_505, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_478, c_503])).
% 3.02/1.48  tff(c_508, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_505])).
% 3.02/1.48  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_316, c_508])).
% 3.02/1.48  tff(c_512, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 3.02/1.48  tff(c_22, plain, (![A_28, B_29]: (m1_connsp_2('#skF_1'(A_28, B_29), A_28, B_29) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.02/1.48  tff(c_615, plain, (![C_158, A_159, B_160]: (m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_connsp_2(C_158, A_159, B_160) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.48  tff(c_618, plain, (![A_28, B_29]: (m1_subset_1('#skF_1'(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(resolution, [status(thm)], [c_22, c_615])).
% 3.02/1.48  tff(c_619, plain, (![C_161, B_162, A_163]: (r2_hidden(C_161, B_162) | ~m1_connsp_2(B_162, A_163, C_161) | ~m1_subset_1(C_161, u1_struct_0(A_163)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.02/1.48  tff(c_632, plain, (![B_169, A_170]: (r2_hidden(B_169, '#skF_1'(A_170, B_169)) | ~m1_subset_1('#skF_1'(A_170, B_169), k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(B_169, u1_struct_0(A_170)) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(resolution, [status(thm)], [c_22, c_619])).
% 3.02/1.48  tff(c_636, plain, (![B_171, A_172]: (r2_hidden(B_171, '#skF_1'(A_172, B_171)) | ~m1_subset_1(B_171, u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_618, c_632])).
% 3.02/1.48  tff(c_623, plain, (![A_164, B_165]: (m1_subset_1('#skF_1'(A_164, B_165), k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_22, c_615])).
% 3.02/1.48  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.48  tff(c_630, plain, (![A_164, A_3, B_165]: (~v1_xboole_0(u1_struct_0(A_164)) | ~r2_hidden(A_3, '#skF_1'(A_164, B_165)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_623, c_6])).
% 3.02/1.48  tff(c_641, plain, (![A_173, B_174]: (~v1_xboole_0(u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_636, c_630])).
% 3.02/1.48  tff(c_644, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_641])).
% 3.02/1.48  tff(c_647, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_512, c_644])).
% 3.02/1.48  tff(c_649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_647])).
% 3.02/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  Inference rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Ref     : 0
% 3.02/1.48  #Sup     : 120
% 3.02/1.48  #Fact    : 0
% 3.02/1.48  #Define  : 0
% 3.02/1.48  #Split   : 12
% 3.02/1.48  #Chain   : 0
% 3.02/1.48  #Close   : 0
% 3.02/1.48  
% 3.02/1.48  Ordering : KBO
% 3.02/1.48  
% 3.02/1.48  Simplification rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Subsume      : 13
% 3.02/1.48  #Demod        : 94
% 3.02/1.48  #Tautology    : 36
% 3.02/1.48  #SimpNegUnit  : 27
% 3.02/1.48  #BackRed      : 2
% 3.02/1.48  
% 3.02/1.48  #Partial instantiations: 0
% 3.02/1.48  #Strategies tried      : 1
% 3.02/1.48  
% 3.02/1.48  Timing (in seconds)
% 3.02/1.48  ----------------------
% 3.02/1.48  Preprocessing        : 0.32
% 3.02/1.48  Parsing              : 0.18
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.34
% 3.02/1.48  Inferencing          : 0.14
% 3.02/1.48  Reduction            : 0.10
% 3.02/1.48  Demodulation         : 0.06
% 3.02/1.48  BG Simplification    : 0.02
% 3.02/1.48  Subsumption          : 0.05
% 3.02/1.48  Abstraction          : 0.02
% 3.02/1.48  MUC search           : 0.00
% 3.02/1.48  Cooper               : 0.00
% 3.02/1.48  Total                : 0.70
% 3.02/1.49  Index Insertion      : 0.00
% 3.02/1.49  Index Deletion       : 0.00
% 3.02/1.49  Index Matching       : 0.00
% 3.02/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
