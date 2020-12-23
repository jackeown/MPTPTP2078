%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:15 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 305 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 972 expanded)
%              Number of equality atoms :    7 (  16 expanded)
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

tff(f_164,negated_conjecture,(
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

tff(f_78,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_92,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_146,axiom,(
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

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,
    ( m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
    | m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_69,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_244,plain,(
    ! [B_105,A_106,C_107] :
      ( r2_hidden(B_105,k1_tops_1(A_106,C_107))
      | ~ m1_connsp_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_105,u1_struct_0(A_106))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_251,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_105)
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_244])).

tff(c_256,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_105)
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_251])).

tff(c_257,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_105)
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_256])).

tff(c_81,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k1_tarski(A_8),k1_zfmisc_1(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [C_92,A_93,B_94] :
      ( m2_connsp_2(C_92,A_93,B_94)
      | ~ r1_tarski(B_94,k1_tops_1(A_93,C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_279,plain,(
    ! [C_112,A_113,A_114] :
      ( m2_connsp_2(C_112,A_113,k1_tarski(A_114))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(k1_tarski(A_114),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | ~ r2_hidden(A_114,k1_tops_1(A_113,C_112)) ) ),
    inference(resolution,[status(thm)],[c_10,c_181])).

tff(c_286,plain,(
    ! [A_114] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_114))
      | ~ m1_subset_1(k1_tarski(A_114),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r2_hidden(A_114,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_279])).

tff(c_292,plain,(
    ! [A_115] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_115))
      | ~ m1_subset_1(k1_tarski(A_115),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_115,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_286])).

tff(c_298,plain,(
    ! [A_116] :
      ( m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_116))
      | ~ r2_hidden(A_116,k1_tops_1('#skF_3','#skF_5'))
      | ~ r2_hidden(A_116,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_292])).

tff(c_90,plain,(
    ! [A_67,B_68] :
      ( k6_domain_1(A_67,B_68) = k1_tarski(B_68)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_102,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_104,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_102])).

tff(c_46,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_110,plain,(
    ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_69,c_46])).

tff(c_311,plain,
    ( ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_298,c_110])).

tff(c_312,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_315,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_312])).

tff(c_318,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_315])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_318])).

tff(c_321,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_337,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_257,c_321])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69,c_337])).

tff(c_345,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_389,plain,(
    ! [C_134,B_135,A_136] :
      ( r2_hidden(C_134,B_135)
      | ~ m1_connsp_2(B_135,A_136,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(A_136))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_393,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_389])).

tff(c_397,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_38,c_393])).

tff(c_398,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_397])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_401,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_398,c_2])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_401])).

tff(c_407,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_418,plain,(
    ! [B_141,A_142] :
      ( v1_xboole_0(B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_142))
      | ~ v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_422,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_418])).

tff(c_423,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_431,plain,(
    ! [A_145,B_146] :
      ( k6_domain_1(A_145,B_146) = k1_tarski(B_146)
      | ~ m1_subset_1(B_146,A_145)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_440,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_431])).

tff(c_445,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_440])).

tff(c_406,plain,(
    m2_connsp_2('#skF_5','#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_446,plain,(
    m2_connsp_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_406])).

tff(c_502,plain,(
    ! [B_168,A_169,C_170] :
      ( r1_tarski(B_168,k1_tops_1(A_169,C_170))
      | ~ m2_connsp_2(C_170,A_169,B_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_509,plain,(
    ! [B_168] :
      ( r1_tarski(B_168,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_502])).

tff(c_515,plain,(
    ! [B_171] :
      ( r1_tarski(B_171,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_509])).

tff(c_543,plain,(
    ! [A_175] :
      ( r1_tarski(k1_tarski(A_175),k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_175))
      | ~ r2_hidden(A_175,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_515])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_548,plain,(
    ! [A_176] :
      ( r2_hidden(A_176,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',k1_tarski(A_176))
      | ~ r2_hidden(A_176,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_543,c_8])).

tff(c_552,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_446,c_548])).

tff(c_553,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_571,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_553])).

tff(c_574,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_571])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_574])).

tff(c_577,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_602,plain,(
    ! [C_183,A_184,B_185] :
      ( m1_connsp_2(C_183,A_184,B_185)
      | ~ r2_hidden(B_185,k1_tops_1(A_184,C_183))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_604,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_577,c_602])).

tff(c_613,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_604])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_407,c_613])).

tff(c_617,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( m1_connsp_2('#skF_2'(A_39,B_40),A_39,B_40)
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_656,plain,(
    ! [C_197,A_198,B_199] :
      ( m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ m1_connsp_2(C_197,A_198,B_199)
      | ~ m1_subset_1(B_199,u1_struct_0(A_198))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_660,plain,(
    ! [A_200,B_201] :
      ( m1_subset_1('#skF_2'(A_200,B_201),k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_32,c_656])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_669,plain,(
    ! [A_202,B_203] :
      ( v1_xboole_0('#skF_2'(A_202,B_203))
      | ~ v1_xboole_0(u1_struct_0(A_202))
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(resolution,[status(thm)],[c_660,c_14])).

tff(c_672,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_669])).

tff(c_675,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_617,c_672])).

tff(c_676,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_675])).

tff(c_659,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1('#skF_2'(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_32,c_656])).

tff(c_677,plain,(
    ! [C_204,B_205,A_206] :
      ( r2_hidden(C_204,B_205)
      | ~ m1_connsp_2(B_205,A_206,C_204)
      | ~ m1_subset_1(C_204,u1_struct_0(A_206))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_681,plain,(
    ! [B_207,A_208] :
      ( r2_hidden(B_207,'#skF_2'(A_208,B_207))
      | ~ m1_subset_1('#skF_2'(A_208,B_207),k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ m1_subset_1(B_207,u1_struct_0(A_208))
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_32,c_677])).

tff(c_685,plain,(
    ! [B_209,A_210] :
      ( r2_hidden(B_209,'#skF_2'(A_210,B_209))
      | ~ m1_subset_1(B_209,u1_struct_0(A_210))
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_659,c_681])).

tff(c_695,plain,(
    ! [A_214,B_215] :
      ( ~ v1_xboole_0('#skF_2'(A_214,B_215))
      | ~ m1_subset_1(B_215,u1_struct_0(A_214))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_685,c_2])).

tff(c_698,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_695])).

tff(c_701,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_676,c_698])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/2.05  
% 4.15/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/2.05  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.15/2.05  
% 4.15/2.05  %Foreground sorts:
% 4.15/2.05  
% 4.15/2.05  
% 4.15/2.05  %Background operators:
% 4.15/2.05  
% 4.15/2.05  
% 4.15/2.05  %Foreground operators:
% 4.15/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.15/2.05  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.15/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.15/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.15/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.15/2.05  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.15/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.15/2.05  tff('#skF_5', type, '#skF_5': $i).
% 4.15/2.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.15/2.05  tff('#skF_3', type, '#skF_3': $i).
% 4.15/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/2.05  tff('#skF_4', type, '#skF_4': $i).
% 4.15/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/2.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.15/2.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.15/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.15/2.05  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 4.15/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/2.05  
% 4.55/2.09  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 4.55/2.09  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.55/2.09  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.55/2.09  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.55/2.09  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.55/2.09  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.55/2.09  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 4.55/2.09  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.55/2.09  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 4.55/2.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.55/2.09  tff(f_129, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.55/2.09  tff(f_106, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.55/2.09  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_52, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_69, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 4.55/2.09  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_244, plain, (![B_105, A_106, C_107]: (r2_hidden(B_105, k1_tops_1(A_106, C_107)) | ~m1_connsp_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_105, u1_struct_0(A_106)) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.55/2.09  tff(c_251, plain, (![B_105]: (r2_hidden(B_105, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_105) | ~m1_subset_1(B_105, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_244])).
% 4.55/2.09  tff(c_256, plain, (![B_105]: (r2_hidden(B_105, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_105) | ~m1_subset_1(B_105, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_251])).
% 4.55/2.09  tff(c_257, plain, (![B_105]: (r2_hidden(B_105, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_105) | ~m1_subset_1(B_105, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_256])).
% 4.55/2.09  tff(c_81, plain, (![B_65, A_66]: (v1_xboole_0(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/2.09  tff(c_89, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_81])).
% 4.55/2.09  tff(c_103, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_89])).
% 4.55/2.09  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.55/2.09  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k1_tarski(A_8), k1_zfmisc_1(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/2.09  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/2.09  tff(c_181, plain, (![C_92, A_93, B_94]: (m2_connsp_2(C_92, A_93, B_94) | ~r1_tarski(B_94, k1_tops_1(A_93, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/2.09  tff(c_279, plain, (![C_112, A_113, A_114]: (m2_connsp_2(C_112, A_113, k1_tarski(A_114)) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(k1_tarski(A_114), k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | ~r2_hidden(A_114, k1_tops_1(A_113, C_112)))), inference(resolution, [status(thm)], [c_10, c_181])).
% 4.55/2.09  tff(c_286, plain, (![A_114]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_114)) | ~m1_subset_1(k1_tarski(A_114), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden(A_114, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_36, c_279])).
% 4.55/2.09  tff(c_292, plain, (![A_115]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_115)) | ~m1_subset_1(k1_tarski(A_115), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_115, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_286])).
% 4.55/2.09  tff(c_298, plain, (![A_116]: (m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_116)) | ~r2_hidden(A_116, k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden(A_116, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_292])).
% 4.55/2.09  tff(c_90, plain, (![A_67, B_68]: (k6_domain_1(A_67, B_68)=k1_tarski(B_68) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.55/2.09  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_90])).
% 4.55/2.09  tff(c_104, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_103, c_102])).
% 4.55/2.09  tff(c_46, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.55/2.09  tff(c_110, plain, (~m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_69, c_46])).
% 4.55/2.09  tff(c_311, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_298, c_110])).
% 4.55/2.09  tff(c_312, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_311])).
% 4.55/2.09  tff(c_315, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_312])).
% 4.55/2.09  tff(c_318, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_315])).
% 4.55/2.09  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_318])).
% 4.55/2.09  tff(c_321, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_311])).
% 4.55/2.09  tff(c_337, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_257, c_321])).
% 4.55/2.09  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_69, c_337])).
% 4.55/2.09  tff(c_345, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_89])).
% 4.55/2.09  tff(c_389, plain, (![C_134, B_135, A_136]: (r2_hidden(C_134, B_135) | ~m1_connsp_2(B_135, A_136, C_134) | ~m1_subset_1(C_134, u1_struct_0(A_136)) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.55/2.09  tff(c_393, plain, (r2_hidden('#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_69, c_389])).
% 4.55/2.09  tff(c_397, plain, (r2_hidden('#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_38, c_393])).
% 4.55/2.09  tff(c_398, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_397])).
% 4.55/2.09  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/2.09  tff(c_401, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_398, c_2])).
% 4.55/2.09  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_345, c_401])).
% 4.55/2.09  tff(c_407, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 4.55/2.09  tff(c_418, plain, (![B_141, A_142]: (v1_xboole_0(B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(A_142)) | ~v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/2.09  tff(c_422, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_418])).
% 4.55/2.09  tff(c_423, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_422])).
% 4.55/2.09  tff(c_431, plain, (![A_145, B_146]: (k6_domain_1(A_145, B_146)=k1_tarski(B_146) | ~m1_subset_1(B_146, A_145) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.55/2.09  tff(c_440, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_431])).
% 4.55/2.09  tff(c_445, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_423, c_440])).
% 4.55/2.09  tff(c_406, plain, (m2_connsp_2('#skF_5', '#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 4.55/2.09  tff(c_446, plain, (m2_connsp_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_406])).
% 4.55/2.09  tff(c_502, plain, (![B_168, A_169, C_170]: (r1_tarski(B_168, k1_tops_1(A_169, C_170)) | ~m2_connsp_2(C_170, A_169, B_168) | ~m1_subset_1(C_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/2.09  tff(c_509, plain, (![B_168]: (r1_tarski(B_168, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_502])).
% 4.55/2.09  tff(c_515, plain, (![B_171]: (r1_tarski(B_171, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_171) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_509])).
% 4.55/2.09  tff(c_543, plain, (![A_175]: (r1_tarski(k1_tarski(A_175), k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_175)) | ~r2_hidden(A_175, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_515])).
% 4.55/2.09  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/2.09  tff(c_548, plain, (![A_176]: (r2_hidden(A_176, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', k1_tarski(A_176)) | ~r2_hidden(A_176, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_543, c_8])).
% 4.55/2.09  tff(c_552, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_446, c_548])).
% 4.55/2.09  tff(c_553, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_552])).
% 4.55/2.09  tff(c_571, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_553])).
% 4.55/2.09  tff(c_574, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_571])).
% 4.55/2.09  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_423, c_574])).
% 4.55/2.09  tff(c_577, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_552])).
% 4.55/2.09  tff(c_602, plain, (![C_183, A_184, B_185]: (m1_connsp_2(C_183, A_184, B_185) | ~r2_hidden(B_185, k1_tops_1(A_184, C_183)) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(A_184))) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.55/2.09  tff(c_604, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_577, c_602])).
% 4.55/2.09  tff(c_613, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_604])).
% 4.55/2.09  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_407, c_613])).
% 4.55/2.09  tff(c_617, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_422])).
% 4.55/2.09  tff(c_32, plain, (![A_39, B_40]: (m1_connsp_2('#skF_2'(A_39, B_40), A_39, B_40) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.55/2.09  tff(c_656, plain, (![C_197, A_198, B_199]: (m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~m1_connsp_2(C_197, A_198, B_199) | ~m1_subset_1(B_199, u1_struct_0(A_198)) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.55/2.09  tff(c_660, plain, (![A_200, B_201]: (m1_subset_1('#skF_2'(A_200, B_201), k1_zfmisc_1(u1_struct_0(A_200))) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(resolution, [status(thm)], [c_32, c_656])).
% 4.55/2.09  tff(c_14, plain, (![B_12, A_10]: (v1_xboole_0(B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/2.09  tff(c_669, plain, (![A_202, B_203]: (v1_xboole_0('#skF_2'(A_202, B_203)) | ~v1_xboole_0(u1_struct_0(A_202)) | ~m1_subset_1(B_203, u1_struct_0(A_202)) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202))), inference(resolution, [status(thm)], [c_660, c_14])).
% 4.55/2.09  tff(c_672, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_669])).
% 4.55/2.09  tff(c_675, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_617, c_672])).
% 4.55/2.09  tff(c_676, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_675])).
% 4.55/2.09  tff(c_659, plain, (![A_39, B_40]: (m1_subset_1('#skF_2'(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_32, c_656])).
% 4.55/2.09  tff(c_677, plain, (![C_204, B_205, A_206]: (r2_hidden(C_204, B_205) | ~m1_connsp_2(B_205, A_206, C_204) | ~m1_subset_1(C_204, u1_struct_0(A_206)) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.55/2.09  tff(c_681, plain, (![B_207, A_208]: (r2_hidden(B_207, '#skF_2'(A_208, B_207)) | ~m1_subset_1('#skF_2'(A_208, B_207), k1_zfmisc_1(u1_struct_0(A_208))) | ~m1_subset_1(B_207, u1_struct_0(A_208)) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(resolution, [status(thm)], [c_32, c_677])).
% 4.55/2.09  tff(c_685, plain, (![B_209, A_210]: (r2_hidden(B_209, '#skF_2'(A_210, B_209)) | ~m1_subset_1(B_209, u1_struct_0(A_210)) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210) | v2_struct_0(A_210))), inference(resolution, [status(thm)], [c_659, c_681])).
% 4.55/2.09  tff(c_695, plain, (![A_214, B_215]: (~v1_xboole_0('#skF_2'(A_214, B_215)) | ~m1_subset_1(B_215, u1_struct_0(A_214)) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(resolution, [status(thm)], [c_685, c_2])).
% 4.55/2.09  tff(c_698, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_695])).
% 4.55/2.09  tff(c_701, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_676, c_698])).
% 4.55/2.09  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_701])).
% 4.55/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/2.09  
% 4.55/2.09  Inference rules
% 4.55/2.09  ----------------------
% 4.55/2.09  #Ref     : 0
% 4.55/2.09  #Sup     : 123
% 4.55/2.09  #Fact    : 0
% 4.55/2.09  #Define  : 0
% 4.55/2.09  #Split   : 12
% 4.55/2.09  #Chain   : 0
% 4.55/2.09  #Close   : 0
% 4.55/2.09  
% 4.55/2.09  Ordering : KBO
% 4.55/2.09  
% 4.55/2.09  Simplification rules
% 4.55/2.09  ----------------------
% 4.55/2.09  #Subsume      : 12
% 4.55/2.09  #Demod        : 92
% 4.55/2.09  #Tautology    : 38
% 4.55/2.09  #SimpNegUnit  : 20
% 4.55/2.09  #BackRed      : 1
% 4.55/2.09  
% 4.55/2.09  #Partial instantiations: 0
% 4.55/2.09  #Strategies tried      : 1
% 4.55/2.09  
% 4.55/2.09  Timing (in seconds)
% 4.55/2.09  ----------------------
% 4.55/2.09  Preprocessing        : 0.53
% 4.55/2.09  Parsing              : 0.28
% 4.55/2.09  CNF conversion       : 0.04
% 4.55/2.09  Main loop            : 0.58
% 4.55/2.09  Inferencing          : 0.24
% 4.55/2.09  Reduction            : 0.16
% 4.55/2.09  Demodulation         : 0.10
% 4.55/2.09  BG Simplification    : 0.03
% 4.55/2.09  Subsumption          : 0.09
% 4.55/2.09  Abstraction          : 0.03
% 4.55/2.09  MUC search           : 0.00
% 4.55/2.09  Cooper               : 0.00
% 4.55/2.09  Total                : 1.19
% 4.55/2.09  Index Insertion      : 0.00
% 4.55/2.09  Index Deletion       : 0.00
% 4.55/2.10  Index Matching       : 0.00
% 4.55/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
