%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 240 expanded)
%              Number of leaves         :   31 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  249 ( 751 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

tff(f_131,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_87,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_49,plain,(
    ! [C_41,B_42,A_43] :
      ( ~ v1_xboole_0(C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_43,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_53,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_55,plain,(
    ! [A_44,B_45] :
      ( k6_domain_1(A_44,B_45) = k1_tarski(B_45)
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_54,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_66,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54])).

tff(c_42,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_92,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_42])).

tff(c_93,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_92])).

tff(c_262,plain,(
    ! [B_79,A_80,C_81] :
      ( r2_hidden(B_79,k1_tops_1(A_80,C_81))
      | ~ m1_connsp_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(B_79,u1_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_273,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_262])).

tff(c_283,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_273])).

tff(c_284,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_283])).

tff(c_71,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k6_domain_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
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

tff(c_224,plain,(
    ! [C_73,A_74,B_75] :
      ( m2_connsp_2(C_73,A_74,B_75)
      | ~ r1_tarski(B_75,k1_tops_1(A_74,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_310,plain,(
    ! [C_87,A_88,A_89] :
      ( m2_connsp_2(C_87,A_88,k1_tarski(A_89))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(k1_tarski(A_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ r2_hidden(A_89,k1_tops_1(A_88,C_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_224])).

tff(c_321,plain,(
    ! [A_89] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_89))
      | ~ m1_subset_1(k1_tarski(A_89),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r2_hidden(A_89,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_26,c_310])).

tff(c_331,plain,(
    ! [A_90] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_90))
      | ~ m1_subset_1(k1_tarski(A_90),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_90,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_321])).

tff(c_334,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_331])).

tff(c_337,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_334])).

tff(c_340,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_284,c_337])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_93,c_340])).

tff(c_345,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_352,plain,(
    ! [A_91,B_92] :
      ( k6_domain_1(A_91,B_92) = k1_tarski(B_92)
      | ~ m1_subset_1(B_92,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_358,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_352])).

tff(c_362,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_358])).

tff(c_346,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_363,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_346])).

tff(c_369,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k6_domain_1(A_93,B_94),k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_94,A_93)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_377,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_369])).

tff(c_381,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_377])).

tff(c_382,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_381])).

tff(c_458,plain,(
    ! [B_117,A_118,C_119] :
      ( r1_tarski(B_117,k1_tops_1(A_118,C_119))
      | ~ m2_connsp_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_469,plain,(
    ! [B_117] :
      ( r1_tarski(B_117,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_458])).

tff(c_479,plain,(
    ! [B_120] :
      ( r1_tarski(B_120,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_469])).

tff(c_490,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4'))
    | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_382,c_479])).

tff(c_507,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_490])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | ~ r1_tarski(k1_tarski(A_1),B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_520,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_507,c_2])).

tff(c_590,plain,(
    ! [C_130,A_131,B_132] :
      ( m1_connsp_2(C_130,A_131,B_132)
      | ~ r2_hidden(B_132,k1_tops_1(A_131,C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_596,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_520,c_590])).

tff(c_607,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_596])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_345,c_607])).

tff(c_611,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_24,plain,(
    ! [A_30,B_31] :
      ( m1_connsp_2('#skF_1'(A_30,B_31),A_30,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_835,plain,(
    ! [C_185,A_186,B_187] :
      ( m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ m1_connsp_2(C_185,A_186,B_187)
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_838,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1('#skF_1'(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_24,c_835])).

tff(c_924,plain,(
    ! [B_207,A_208,C_209] :
      ( r2_hidden(B_207,k1_tops_1(A_208,C_209))
      | ~ m1_connsp_2(C_209,A_208,B_207)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ m1_subset_1(B_207,u1_struct_0(A_208))
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1016,plain,(
    ! [B_223,A_224,B_225] :
      ( r2_hidden(B_223,k1_tops_1(A_224,'#skF_1'(A_224,B_225)))
      | ~ m1_connsp_2('#skF_1'(A_224,B_225),A_224,B_223)
      | ~ m1_subset_1(B_223,u1_struct_0(A_224))
      | ~ m1_subset_1(B_225,u1_struct_0(A_224))
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(resolution,[status(thm)],[c_838,c_924])).

tff(c_807,plain,(
    ! [A_176,B_177] :
      ( m1_subset_1(k1_tops_1(A_176,B_177),k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_814,plain,(
    ! [A_176,A_3,B_177] :
      ( ~ v1_xboole_0(u1_struct_0(A_176))
      | ~ r2_hidden(A_3,k1_tops_1(A_176,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(resolution,[status(thm)],[c_807,c_6])).

tff(c_1043,plain,(
    ! [A_244,B_245,B_246] :
      ( ~ v1_xboole_0(u1_struct_0(A_244))
      | ~ m1_subset_1('#skF_1'(A_244,B_245),k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ m1_connsp_2('#skF_1'(A_244,B_245),A_244,B_246)
      | ~ m1_subset_1(B_246,u1_struct_0(A_244))
      | ~ m1_subset_1(B_245,u1_struct_0(A_244))
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_1016,c_814])).

tff(c_1047,plain,(
    ! [A_247,B_248,B_249] :
      ( ~ v1_xboole_0(u1_struct_0(A_247))
      | ~ m1_connsp_2('#skF_1'(A_247,B_248),A_247,B_249)
      | ~ m1_subset_1(B_249,u1_struct_0(A_247))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_838,c_1043])).

tff(c_1052,plain,(
    ! [A_250,B_251] :
      ( ~ v1_xboole_0(u1_struct_0(A_250))
      | ~ m1_subset_1(B_251,u1_struct_0(A_250))
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(resolution,[status(thm)],[c_24,c_1047])).

tff(c_1055,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1052])).

tff(c_1058,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_611,c_1055])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:32:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.59  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.28/1.59  
% 3.28/1.59  %Foreground sorts:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Background operators:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Foreground operators:
% 3.28/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.28/1.59  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.28/1.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.28/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.28/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.28/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.59  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.28/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.59  
% 3.28/1.61  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.28/1.61  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.28/1.61  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.28/1.61  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.28/1.61  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.28/1.61  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.28/1.61  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.28/1.61  tff(f_113, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.28/1.61  tff(f_101, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.28/1.61  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.28/1.61  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_49, plain, (![C_41, B_42, A_43]: (~v1_xboole_0(C_41) | ~m1_subset_1(B_42, k1_zfmisc_1(C_41)) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.28/1.61  tff(c_52, plain, (![A_43]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_49])).
% 3.28/1.61  tff(c_53, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.28/1.61  tff(c_55, plain, (![A_44, B_45]: (k6_domain_1(A_44, B_45)=k1_tarski(B_45) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.28/1.61  tff(c_61, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_55])).
% 3.28/1.61  tff(c_65, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_61])).
% 3.28/1.61  tff(c_36, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_54, plain, (~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.28/1.61  tff(c_66, plain, (~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54])).
% 3.28/1.61  tff(c_42, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.28/1.61  tff(c_92, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_42])).
% 3.28/1.61  tff(c_93, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_92])).
% 3.28/1.61  tff(c_262, plain, (![B_79, A_80, C_81]: (r2_hidden(B_79, k1_tops_1(A_80, C_81)) | ~m1_connsp_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(B_79, u1_struct_0(A_80)) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.61  tff(c_273, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_262])).
% 3.28/1.61  tff(c_283, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_273])).
% 3.28/1.61  tff(c_284, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_283])).
% 3.28/1.61  tff(c_71, plain, (![A_46, B_47]: (m1_subset_1(k6_domain_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.61  tff(c_79, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_71])).
% 3.28/1.61  tff(c_83, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_79])).
% 3.28/1.61  tff(c_84, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_53, c_83])).
% 3.28/1.61  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.61  tff(c_224, plain, (![C_73, A_74, B_75]: (m2_connsp_2(C_73, A_74, B_75) | ~r1_tarski(B_75, k1_tops_1(A_74, C_73)) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.28/1.61  tff(c_310, plain, (![C_87, A_88, A_89]: (m2_connsp_2(C_87, A_88, k1_tarski(A_89)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(k1_tarski(A_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~r2_hidden(A_89, k1_tops_1(A_88, C_87)))), inference(resolution, [status(thm)], [c_4, c_224])).
% 3.28/1.61  tff(c_321, plain, (![A_89]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_89)) | ~m1_subset_1(k1_tarski(A_89), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden(A_89, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_26, c_310])).
% 3.28/1.61  tff(c_331, plain, (![A_90]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_90)) | ~m1_subset_1(k1_tarski(A_90), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_90, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_321])).
% 3.28/1.61  tff(c_334, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_331])).
% 3.28/1.61  tff(c_337, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_334])).
% 3.28/1.61  tff(c_340, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_284, c_337])).
% 3.28/1.61  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_93, c_340])).
% 3.28/1.61  tff(c_345, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.28/1.61  tff(c_352, plain, (![A_91, B_92]: (k6_domain_1(A_91, B_92)=k1_tarski(B_92) | ~m1_subset_1(B_92, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.28/1.61  tff(c_358, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_352])).
% 3.28/1.61  tff(c_362, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_358])).
% 3.28/1.61  tff(c_346, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_36])).
% 3.28/1.61  tff(c_363, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_346])).
% 3.28/1.61  tff(c_369, plain, (![A_93, B_94]: (m1_subset_1(k6_domain_1(A_93, B_94), k1_zfmisc_1(A_93)) | ~m1_subset_1(B_94, A_93) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.61  tff(c_377, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_362, c_369])).
% 3.28/1.61  tff(c_381, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_377])).
% 3.28/1.61  tff(c_382, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_53, c_381])).
% 3.28/1.61  tff(c_458, plain, (![B_117, A_118, C_119]: (r1_tarski(B_117, k1_tops_1(A_118, C_119)) | ~m2_connsp_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.28/1.61  tff(c_469, plain, (![B_117]: (r1_tarski(B_117, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_458])).
% 3.28/1.61  tff(c_479, plain, (![B_120]: (r1_tarski(B_120, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_469])).
% 3.28/1.61  tff(c_490, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_382, c_479])).
% 3.28/1.61  tff(c_507, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_490])).
% 3.28/1.61  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | ~r1_tarski(k1_tarski(A_1), B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.61  tff(c_520, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_507, c_2])).
% 3.28/1.61  tff(c_590, plain, (![C_130, A_131, B_132]: (m1_connsp_2(C_130, A_131, B_132) | ~r2_hidden(B_132, k1_tops_1(A_131, C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.61  tff(c_596, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_520, c_590])).
% 3.28/1.61  tff(c_607, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_596])).
% 3.28/1.61  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_345, c_607])).
% 3.28/1.61  tff(c_611, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 3.28/1.61  tff(c_24, plain, (![A_30, B_31]: (m1_connsp_2('#skF_1'(A_30, B_31), A_30, B_31) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.61  tff(c_835, plain, (![C_185, A_186, B_187]: (m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~m1_connsp_2(C_185, A_186, B_187) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.28/1.61  tff(c_838, plain, (![A_30, B_31]: (m1_subset_1('#skF_1'(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(resolution, [status(thm)], [c_24, c_835])).
% 3.28/1.61  tff(c_924, plain, (![B_207, A_208, C_209]: (r2_hidden(B_207, k1_tops_1(A_208, C_209)) | ~m1_connsp_2(C_209, A_208, B_207) | ~m1_subset_1(C_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~m1_subset_1(B_207, u1_struct_0(A_208)) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.61  tff(c_1016, plain, (![B_223, A_224, B_225]: (r2_hidden(B_223, k1_tops_1(A_224, '#skF_1'(A_224, B_225))) | ~m1_connsp_2('#skF_1'(A_224, B_225), A_224, B_223) | ~m1_subset_1(B_223, u1_struct_0(A_224)) | ~m1_subset_1(B_225, u1_struct_0(A_224)) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(resolution, [status(thm)], [c_838, c_924])).
% 3.28/1.61  tff(c_807, plain, (![A_176, B_177]: (m1_subset_1(k1_tops_1(A_176, B_177), k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.61  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.28/1.61  tff(c_814, plain, (![A_176, A_3, B_177]: (~v1_xboole_0(u1_struct_0(A_176)) | ~r2_hidden(A_3, k1_tops_1(A_176, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(resolution, [status(thm)], [c_807, c_6])).
% 3.28/1.61  tff(c_1043, plain, (![A_244, B_245, B_246]: (~v1_xboole_0(u1_struct_0(A_244)) | ~m1_subset_1('#skF_1'(A_244, B_245), k1_zfmisc_1(u1_struct_0(A_244))) | ~m1_connsp_2('#skF_1'(A_244, B_245), A_244, B_246) | ~m1_subset_1(B_246, u1_struct_0(A_244)) | ~m1_subset_1(B_245, u1_struct_0(A_244)) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_1016, c_814])).
% 3.28/1.61  tff(c_1047, plain, (![A_247, B_248, B_249]: (~v1_xboole_0(u1_struct_0(A_247)) | ~m1_connsp_2('#skF_1'(A_247, B_248), A_247, B_249) | ~m1_subset_1(B_249, u1_struct_0(A_247)) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(resolution, [status(thm)], [c_838, c_1043])).
% 3.28/1.61  tff(c_1052, plain, (![A_250, B_251]: (~v1_xboole_0(u1_struct_0(A_250)) | ~m1_subset_1(B_251, u1_struct_0(A_250)) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(resolution, [status(thm)], [c_24, c_1047])).
% 3.28/1.61  tff(c_1055, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1052])).
% 3.28/1.61  tff(c_1058, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_611, c_1055])).
% 3.28/1.61  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1058])).
% 3.28/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.61  
% 3.28/1.61  Inference rules
% 3.28/1.61  ----------------------
% 3.28/1.61  #Ref     : 0
% 3.28/1.61  #Sup     : 209
% 3.28/1.61  #Fact    : 0
% 3.28/1.61  #Define  : 0
% 3.28/1.61  #Split   : 13
% 3.28/1.61  #Chain   : 0
% 3.28/1.61  #Close   : 0
% 3.28/1.61  
% 3.28/1.61  Ordering : KBO
% 3.28/1.61  
% 3.28/1.61  Simplification rules
% 3.28/1.61  ----------------------
% 3.28/1.61  #Subsume      : 16
% 3.28/1.61  #Demod        : 153
% 3.28/1.61  #Tautology    : 63
% 3.28/1.61  #SimpNegUnit  : 33
% 3.28/1.61  #BackRed      : 2
% 3.28/1.61  
% 3.28/1.61  #Partial instantiations: 0
% 3.28/1.61  #Strategies tried      : 1
% 3.28/1.61  
% 3.28/1.61  Timing (in seconds)
% 3.28/1.61  ----------------------
% 3.28/1.61  Preprocessing        : 0.35
% 3.28/1.61  Parsing              : 0.18
% 3.28/1.61  CNF conversion       : 0.03
% 3.28/1.61  Main loop            : 0.45
% 3.28/1.61  Inferencing          : 0.18
% 3.28/1.61  Reduction            : 0.13
% 3.28/1.62  Demodulation         : 0.08
% 3.28/1.62  BG Simplification    : 0.03
% 3.28/1.62  Subsumption          : 0.07
% 3.28/1.62  Abstraction          : 0.02
% 3.28/1.62  MUC search           : 0.00
% 3.28/1.62  Cooper               : 0.00
% 3.28/1.62  Total                : 0.84
% 3.28/1.62  Index Insertion      : 0.00
% 3.28/1.62  Index Deletion       : 0.00
% 3.28/1.62  Index Matching       : 0.00
% 3.28/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
