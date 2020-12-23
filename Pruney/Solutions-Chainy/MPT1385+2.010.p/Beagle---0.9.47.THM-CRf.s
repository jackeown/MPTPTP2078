%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:16 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 264 expanded)
%              Number of leaves         :   31 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 799 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_98,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_71,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_190,plain,(
    ! [B_68,A_69,C_70] :
      ( r2_hidden(B_68,k1_tops_1(A_69,C_70))
      | ~ m1_connsp_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_68,u1_struct_0(A_69))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_198,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_190])).

tff(c_203,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_198])).

tff(c_204,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_203])).

tff(c_62,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_72,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [C_60,A_61,B_62] :
      ( m2_connsp_2(C_60,A_61,B_62)
      | ~ r1_tarski(B_62,k1_tops_1(A_61,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_247,plain,(
    ! [C_85,A_86,A_87] :
      ( m2_connsp_2(C_85,A_86,k1_tarski(A_87))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(k1_tarski(A_87),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | ~ r2_hidden(A_87,k1_tops_1(A_86,C_85)) ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_255,plain,(
    ! [A_87] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_87))
      | ~ m1_subset_1(k1_tarski(A_87),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_87,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_262,plain,(
    ! [A_91] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_91))
      | ~ m1_subset_1(k1_tarski(A_91),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_91,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_255])).

tff(c_272,plain,(
    ! [A_92] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_92))
      | ~ r2_hidden(A_92,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_92,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_262])).

tff(c_99,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_99])).

tff(c_119,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_111])).

tff(c_44,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_87,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_44])).

tff(c_120,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_87])).

tff(c_280,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_272,c_120])).

tff(c_281,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_284,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_281])).

tff(c_287,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_284])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_287])).

tff(c_290,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_300,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_204,c_290])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_71,c_300])).

tff(c_309,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_312,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_309,c_20])).

tff(c_315,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_312])).

tff(c_318,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_315])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_318])).

tff(c_324,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_325,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_350,plain,(
    ! [A_107,B_108] :
      ( k6_domain_1(A_107,B_108) = k1_tarski(B_108)
      | ~ m1_subset_1(B_108,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_362,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_350])).

tff(c_370,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_362])).

tff(c_323,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_371,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_323])).

tff(c_395,plain,(
    ! [B_117,A_118,C_119] :
      ( r1_tarski(B_117,k1_tops_1(A_118,C_119))
      | ~ m2_connsp_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_403,plain,(
    ! [B_117] :
      ( r1_tarski(B_117,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_395])).

tff(c_409,plain,(
    ! [B_120] :
      ( r1_tarski(B_120,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_403])).

tff(c_425,plain,(
    ! [A_121] :
      ( r1_tarski(k1_tarski(A_121),k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_121))
      | ~ r2_hidden(A_121,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_409])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | ~ r1_tarski(k1_tarski(A_2),B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_435,plain,(
    ! [A_122] :
      ( r2_hidden(A_122,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_122))
      | ~ r2_hidden(A_122,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_425,c_4])).

tff(c_439,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_371,c_435])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_443,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_440])).

tff(c_446,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_443])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_446])).

tff(c_449,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_483,plain,(
    ! [C_127,A_128,B_129] :
      ( m1_connsp_2(C_127,A_128,B_129)
      | ~ r2_hidden(B_129,k1_tops_1(A_128,C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_487,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_449,c_483])).

tff(c_497,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_487])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_324,c_497])).

tff(c_501,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_504,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_501,c_20])).

tff(c_507,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_504])).

tff(c_510,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_507])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.68/1.42  
% 2.68/1.42  %Foreground sorts:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Background operators:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Foreground operators:
% 2.68/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.42  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.68/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.42  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.68/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.42  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.68/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.42  
% 2.96/1.44  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 2.96/1.44  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.96/1.44  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.96/1.44  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.96/1.44  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.96/1.44  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.96/1.44  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.96/1.44  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.96/1.44  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.96/1.44  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.96/1.44  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_50, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_71, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 2.96/1.44  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_190, plain, (![B_68, A_69, C_70]: (r2_hidden(B_68, k1_tops_1(A_69, C_70)) | ~m1_connsp_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_68, u1_struct_0(A_69)) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.96/1.44  tff(c_198, plain, (![B_68]: (r2_hidden(B_68, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_68) | ~m1_subset_1(B_68, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_190])).
% 2.96/1.44  tff(c_203, plain, (![B_68]: (r2_hidden(B_68, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_68) | ~m1_subset_1(B_68, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_198])).
% 2.96/1.44  tff(c_204, plain, (![B_68]: (r2_hidden(B_68, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_68) | ~m1_subset_1(B_68, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_42, c_203])).
% 2.96/1.44  tff(c_62, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.96/1.44  tff(c_70, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.96/1.44  tff(c_72, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_70])).
% 2.96/1.44  tff(c_10, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.96/1.44  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.44  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.44  tff(c_145, plain, (![C_60, A_61, B_62]: (m2_connsp_2(C_60, A_61, B_62) | ~r1_tarski(B_62, k1_tops_1(A_61, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.96/1.44  tff(c_247, plain, (![C_85, A_86, A_87]: (m2_connsp_2(C_85, A_86, k1_tarski(A_87)) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(k1_tarski(A_87), k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | ~r2_hidden(A_87, k1_tops_1(A_86, C_85)))), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.96/1.44  tff(c_255, plain, (![A_87]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_87)) | ~m1_subset_1(k1_tarski(A_87), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_87, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_34, c_247])).
% 2.96/1.44  tff(c_262, plain, (![A_91]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_91)) | ~m1_subset_1(k1_tarski(A_91), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_91, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_255])).
% 2.96/1.44  tff(c_272, plain, (![A_92]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_92)) | ~r2_hidden(A_92, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_92, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_262])).
% 2.96/1.44  tff(c_99, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.96/1.44  tff(c_111, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_99])).
% 2.96/1.44  tff(c_119, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_111])).
% 2.96/1.44  tff(c_44, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.96/1.44  tff(c_87, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_44])).
% 2.96/1.44  tff(c_120, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_87])).
% 2.96/1.44  tff(c_280, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_272, c_120])).
% 2.96/1.44  tff(c_281, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_280])).
% 2.96/1.44  tff(c_284, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_281])).
% 2.96/1.44  tff(c_287, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_284])).
% 2.96/1.44  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_287])).
% 2.96/1.44  tff(c_290, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_280])).
% 2.96/1.44  tff(c_300, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_204, c_290])).
% 2.96/1.44  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_71, c_300])).
% 2.96/1.44  tff(c_309, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_70])).
% 2.96/1.44  tff(c_20, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.44  tff(c_312, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_309, c_20])).
% 2.96/1.44  tff(c_315, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_312])).
% 2.96/1.44  tff(c_318, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_315])).
% 2.96/1.44  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_318])).
% 2.96/1.44  tff(c_324, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 2.96/1.44  tff(c_325, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_70])).
% 2.96/1.44  tff(c_350, plain, (![A_107, B_108]: (k6_domain_1(A_107, B_108)=k1_tarski(B_108) | ~m1_subset_1(B_108, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.96/1.44  tff(c_362, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_350])).
% 2.96/1.44  tff(c_370, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_325, c_362])).
% 2.96/1.44  tff(c_323, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 2.96/1.44  tff(c_371, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_323])).
% 2.96/1.44  tff(c_395, plain, (![B_117, A_118, C_119]: (r1_tarski(B_117, k1_tops_1(A_118, C_119)) | ~m2_connsp_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.96/1.44  tff(c_403, plain, (![B_117]: (r1_tarski(B_117, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_395])).
% 2.96/1.44  tff(c_409, plain, (![B_120]: (r1_tarski(B_120, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_403])).
% 2.96/1.44  tff(c_425, plain, (![A_121]: (r1_tarski(k1_tarski(A_121), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_121)) | ~r2_hidden(A_121, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_409])).
% 2.96/1.44  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | ~r1_tarski(k1_tarski(A_2), B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.44  tff(c_435, plain, (![A_122]: (r2_hidden(A_122, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_122)) | ~r2_hidden(A_122, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_425, c_4])).
% 2.96/1.44  tff(c_439, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_371, c_435])).
% 2.96/1.44  tff(c_440, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_439])).
% 2.96/1.44  tff(c_443, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_440])).
% 2.96/1.44  tff(c_446, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_443])).
% 2.96/1.44  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_446])).
% 2.96/1.44  tff(c_449, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_439])).
% 2.96/1.44  tff(c_483, plain, (![C_127, A_128, B_129]: (m1_connsp_2(C_127, A_128, B_129) | ~r2_hidden(B_129, k1_tops_1(A_128, C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.96/1.44  tff(c_487, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_449, c_483])).
% 2.96/1.44  tff(c_497, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_487])).
% 2.96/1.44  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_324, c_497])).
% 2.96/1.44  tff(c_501, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_70])).
% 2.96/1.44  tff(c_504, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_501, c_20])).
% 2.96/1.44  tff(c_507, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_504])).
% 2.96/1.44  tff(c_510, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_507])).
% 2.96/1.44  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_510])).
% 2.96/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.44  
% 2.96/1.44  Inference rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Ref     : 0
% 2.96/1.44  #Sup     : 88
% 2.96/1.44  #Fact    : 0
% 2.96/1.44  #Define  : 0
% 2.96/1.44  #Split   : 11
% 2.96/1.44  #Chain   : 0
% 2.96/1.44  #Close   : 0
% 2.96/1.44  
% 2.96/1.44  Ordering : KBO
% 2.96/1.44  
% 2.96/1.44  Simplification rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Subsume      : 5
% 2.96/1.44  #Demod        : 44
% 2.96/1.44  #Tautology    : 34
% 2.96/1.44  #SimpNegUnit  : 16
% 2.96/1.44  #BackRed      : 2
% 2.96/1.44  
% 2.96/1.44  #Partial instantiations: 0
% 2.96/1.44  #Strategies tried      : 1
% 2.96/1.44  
% 2.96/1.44  Timing (in seconds)
% 2.96/1.44  ----------------------
% 2.96/1.44  Preprocessing        : 0.34
% 2.96/1.44  Parsing              : 0.19
% 2.96/1.44  CNF conversion       : 0.02
% 2.96/1.44  Main loop            : 0.30
% 2.96/1.44  Inferencing          : 0.12
% 2.96/1.45  Reduction            : 0.08
% 2.96/1.45  Demodulation         : 0.06
% 2.96/1.45  BG Simplification    : 0.02
% 2.96/1.45  Subsumption          : 0.05
% 2.96/1.45  Abstraction          : 0.02
% 2.96/1.45  MUC search           : 0.00
% 2.96/1.45  Cooper               : 0.00
% 2.96/1.45  Total                : 0.69
% 2.96/1.45  Index Insertion      : 0.00
% 2.96/1.45  Index Deletion       : 0.00
% 2.96/1.45  Index Matching       : 0.00
% 2.96/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
