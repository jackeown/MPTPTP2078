%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:16 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 578 expanded)
%              Number of leaves         :   37 ( 215 expanded)
%              Depth                    :   13
%              Number of atoms          :  303 (1573 expanded)
%              Number of equality atoms :   11 ( 166 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_82,axiom,(
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

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_96,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_14,c_63])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_75,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_52,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_73,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_295,plain,(
    ! [B_113,A_114,C_115] :
      ( r2_hidden(B_113,k1_tops_1(A_114,C_115))
      | ~ m1_connsp_2(C_115,A_114,B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(B_113,u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_302,plain,(
    ! [B_113,C_115] :
      ( r2_hidden(B_113,k1_tops_1('#skF_2',C_115))
      | ~ m1_connsp_2(C_115,'#skF_2',B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_295])).

tff(c_306,plain,(
    ! [B_113,C_115] :
      ( r2_hidden(B_113,k1_tops_1('#skF_2',C_115))
      | ~ m1_connsp_2(C_115,'#skF_2',B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_113,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_72,c_302])).

tff(c_319,plain,(
    ! [B_117,C_118] :
      ( r2_hidden(B_117,k1_tops_1('#skF_2',C_118))
      | ~ m1_connsp_2(C_118,'#skF_2',B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_117,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_306])).

tff(c_329,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_74,c_319])).

tff(c_164,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ m1_connsp_2(B_81,A_82,C_80)
      | ~ m1_subset_1(C_80,u1_struct_0(A_82))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_168,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_164])).

tff(c_172,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_74,c_72,c_75,c_72,c_168])).

tff(c_173,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_172])).

tff(c_8,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_3',A_83)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_181,plain,(
    r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_177])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k1_tarski(A_8),k1_zfmisc_1(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,(
    ! [C_93,A_94,B_95] :
      ( m2_connsp_2(C_93,A_94,B_95)
      | ~ r1_tarski(B_95,k1_tops_1(A_94,C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_410,plain,(
    ! [C_148,A_149,A_150] :
      ( m2_connsp_2(C_148,A_149,k1_tarski(A_150))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(k1_tarski(A_150),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | ~ r2_hidden(A_150,k1_tops_1(A_149,C_148)) ) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_417,plain,(
    ! [C_148,A_150] :
      ( m2_connsp_2(C_148,'#skF_2',k1_tarski(A_150))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_tarski(A_150),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r2_hidden(A_150,k1_tops_1('#skF_2',C_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_410])).

tff(c_437,plain,(
    ! [C_153,A_154] :
      ( m2_connsp_2(C_153,'#skF_2',k1_tarski(A_154))
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_tarski(A_154),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ r2_hidden(A_154,k1_tops_1('#skF_2',C_153)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_72,c_417])).

tff(c_448,plain,(
    ! [A_155] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_155))
      | ~ m1_subset_1(k1_tarski(A_155),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ r2_hidden(A_155,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_74,c_437])).

tff(c_454,plain,(
    ! [A_156] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_156))
      | ~ r2_hidden(A_156,k1_tops_1('#skF_2','#skF_4'))
      | ~ r2_hidden(A_156,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_448])).

tff(c_91,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_75,c_91])).

tff(c_104,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k2_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_110,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_107])).

tff(c_113,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_110])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113])).

tff(c_118,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_46,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_90,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73,c_46])).

tff(c_121,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_90])).

tff(c_462,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_454,c_121])).

tff(c_469,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_462])).

tff(c_477,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_329,c_469])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_73,c_477])).

tff(c_483,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_485,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_484,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36])).

tff(c_32,plain,(
    ! [A_37,B_38] :
      ( m1_connsp_2('#skF_1'(A_37,B_38),A_37,B_38)
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_553,plain,(
    ! [C_178,A_179,B_180] :
      ( m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_connsp_2(C_178,A_179,B_180)
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_561,plain,(
    ! [A_184,B_185] :
      ( m1_subset_1('#skF_1'(A_184,B_185),k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_32,c_553])).

tff(c_567,plain,(
    ! [B_185] :
      ( m1_subset_1('#skF_1'('#skF_2',B_185),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_561])).

tff(c_570,plain,(
    ! [B_185] :
      ( m1_subset_1('#skF_1'('#skF_2',B_185),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_185,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_72,c_567])).

tff(c_571,plain,(
    ! [B_185] :
      ( m1_subset_1('#skF_1'('#skF_2',B_185),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_185,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_570])).

tff(c_557,plain,(
    ! [C_181,B_182,A_183] :
      ( r2_hidden(C_181,B_182)
      | ~ m1_connsp_2(B_182,A_183,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_183))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_578,plain,(
    ! [B_187,A_188] :
      ( r2_hidden(B_187,'#skF_1'(A_188,B_187))
      | ~ m1_subset_1('#skF_1'(A_188,B_187),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_187,u1_struct_0(A_188))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_32,c_557])).

tff(c_582,plain,(
    ! [B_187] :
      ( r2_hidden(B_187,'#skF_1'('#skF_2',B_187))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_187),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_578])).

tff(c_585,plain,(
    ! [B_187] :
      ( r2_hidden(B_187,'#skF_1'('#skF_2',B_187))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_187),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_187,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_72,c_582])).

tff(c_587,plain,(
    ! [B_189] :
      ( r2_hidden(B_189,'#skF_1'('#skF_2',B_189))
      | ~ m1_subset_1('#skF_1'('#skF_2',B_189),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_189,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_585])).

tff(c_591,plain,(
    ! [B_190] :
      ( r2_hidden(B_190,'#skF_1'('#skF_2',B_190))
      | ~ m1_subset_1(B_190,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_571,c_587])).

tff(c_595,plain,(
    ! [B_191,A_192] :
      ( r2_hidden(B_191,A_192)
      | ~ m1_subset_1('#skF_1'('#skF_2',B_191),k1_zfmisc_1(A_192))
      | ~ m1_subset_1(B_191,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_591,c_8])).

tff(c_603,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_185,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_571,c_595])).

tff(c_501,plain,(
    ! [A_166,B_167] :
      ( k6_domain_1(A_166,B_167) = k1_tarski(B_167)
      | ~ m1_subset_1(B_167,A_166)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_513,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_485,c_501])).

tff(c_514,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_517,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_514,c_16])).

tff(c_520,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_517])).

tff(c_523,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_520])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_523])).

tff(c_528,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_482,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_497,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_482])).

tff(c_531,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_497])).

tff(c_644,plain,(
    ! [B_206,A_207,C_208] :
      ( r1_tarski(B_206,k1_tops_1(A_207,C_208))
      | ~ m2_connsp_2(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_651,plain,(
    ! [B_206,C_208] :
      ( r1_tarski(B_206,k1_tops_1('#skF_2',C_208))
      | ~ m2_connsp_2(C_208,'#skF_2',B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_644])).

tff(c_662,plain,(
    ! [B_212,C_213] :
      ( r1_tarski(B_212,k1_tops_1('#skF_2',C_213))
      | ~ m2_connsp_2(C_213,'#skF_2',B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_72,c_651])).

tff(c_673,plain,(
    ! [B_214] :
      ( r1_tarski(B_214,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_484,c_662])).

tff(c_689,plain,(
    ! [A_218] :
      ( r1_tarski(k1_tarski(A_218),k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_218))
      | ~ r2_hidden(A_218,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_673])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | ~ r1_tarski(k1_tarski(A_2),B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,(
    ! [A_219] :
      ( r2_hidden(A_219,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_219))
      | ~ r2_hidden(A_219,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_689,c_4])).

tff(c_703,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_531,c_699])).

tff(c_704,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_713,plain,(
    ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_603,c_704])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_713])).

tff(c_718,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_20,plain,(
    ! [C_21,A_15,B_19] :
      ( m1_connsp_2(C_21,A_15,B_19)
      | ~ r2_hidden(B_19,k1_tops_1(A_15,C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_724,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_718,c_20])).

tff(c_729,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_485,c_72,c_484,c_72,c_724])).

tff(c_731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_483,c_729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:57:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  
% 3.22/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.52  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.22/1.52  
% 3.22/1.52  %Foreground sorts:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Background operators:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Foreground operators:
% 3.22/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.52  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.22/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.22/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.22/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.52  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.22/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.52  
% 3.41/1.54  tff(f_168, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.41/1.54  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.41/1.54  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.41/1.54  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.41/1.54  tff(f_150, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.41/1.54  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.41/1.54  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.41/1.54  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.41/1.54  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.41/1.54  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.41/1.54  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.41/1.54  tff(f_133, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.41/1.54  tff(f_110, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.41/1.54  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.54  tff(c_63, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.54  tff(c_68, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_14, c_63])).
% 3.41/1.54  tff(c_72, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.41/1.54  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_75, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38])).
% 3.41/1.54  tff(c_52, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_73, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.41/1.54  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36])).
% 3.41/1.54  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_295, plain, (![B_113, A_114, C_115]: (r2_hidden(B_113, k1_tops_1(A_114, C_115)) | ~m1_connsp_2(C_115, A_114, B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(B_113, u1_struct_0(A_114)) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.41/1.54  tff(c_302, plain, (![B_113, C_115]: (r2_hidden(B_113, k1_tops_1('#skF_2', C_115)) | ~m1_connsp_2(C_115, '#skF_2', B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_113, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_295])).
% 3.41/1.54  tff(c_306, plain, (![B_113, C_115]: (r2_hidden(B_113, k1_tops_1('#skF_2', C_115)) | ~m1_connsp_2(C_115, '#skF_2', B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_113, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_72, c_302])).
% 3.41/1.54  tff(c_319, plain, (![B_117, C_118]: (r2_hidden(B_117, k1_tops_1('#skF_2', C_118)) | ~m1_connsp_2(C_118, '#skF_2', B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_117, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_306])).
% 3.41/1.54  tff(c_329, plain, (![B_117]: (r2_hidden(B_117, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_74, c_319])).
% 3.41/1.54  tff(c_164, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~m1_connsp_2(B_81, A_82, C_80) | ~m1_subset_1(C_80, u1_struct_0(A_82)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.41/1.54  tff(c_168, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_73, c_164])).
% 3.41/1.54  tff(c_172, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_74, c_72, c_75, c_72, c_168])).
% 3.41/1.54  tff(c_173, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_172])).
% 3.41/1.54  tff(c_8, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.54  tff(c_177, plain, (![A_83]: (r2_hidden('#skF_3', A_83) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_173, c_8])).
% 3.41/1.54  tff(c_181, plain, (r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_177])).
% 3.41/1.54  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k1_tarski(A_8), k1_zfmisc_1(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.41/1.54  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.54  tff(c_220, plain, (![C_93, A_94, B_95]: (m2_connsp_2(C_93, A_94, B_95) | ~r1_tarski(B_95, k1_tops_1(A_94, C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.41/1.54  tff(c_410, plain, (![C_148, A_149, A_150]: (m2_connsp_2(C_148, A_149, k1_tarski(A_150)) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(k1_tarski(A_150), k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | ~r2_hidden(A_150, k1_tops_1(A_149, C_148)))), inference(resolution, [status(thm)], [c_6, c_220])).
% 3.41/1.54  tff(c_417, plain, (![C_148, A_150]: (m2_connsp_2(C_148, '#skF_2', k1_tarski(A_150)) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k1_tarski(A_150), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden(A_150, k1_tops_1('#skF_2', C_148)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_410])).
% 3.41/1.54  tff(c_437, plain, (![C_153, A_154]: (m2_connsp_2(C_153, '#skF_2', k1_tarski(A_154)) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k1_tarski(A_154), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~r2_hidden(A_154, k1_tops_1('#skF_2', C_153)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_72, c_417])).
% 3.41/1.54  tff(c_448, plain, (![A_155]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_155)) | ~m1_subset_1(k1_tarski(A_155), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~r2_hidden(A_155, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_74, c_437])).
% 3.41/1.54  tff(c_454, plain, (![A_156]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_156)) | ~r2_hidden(A_156, k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden(A_156, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_448])).
% 3.41/1.54  tff(c_91, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.54  tff(c_103, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_75, c_91])).
% 3.41/1.54  tff(c_104, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_103])).
% 3.41/1.54  tff(c_16, plain, (![A_12]: (~v1_xboole_0(k2_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.41/1.54  tff(c_107, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_104, c_16])).
% 3.41/1.54  tff(c_110, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_107])).
% 3.41/1.54  tff(c_113, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_110])).
% 3.41/1.54  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_113])).
% 3.41/1.54  tff(c_118, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 3.41/1.54  tff(c_46, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.41/1.54  tff(c_90, plain, (~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_73, c_46])).
% 3.49/1.54  tff(c_121, plain, (~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_90])).
% 3.49/1.54  tff(c_462, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_454, c_121])).
% 3.49/1.54  tff(c_469, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_462])).
% 3.49/1.54  tff(c_477, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_329, c_469])).
% 3.49/1.54  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_73, c_477])).
% 3.49/1.54  tff(c_483, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.49/1.54  tff(c_485, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38])).
% 3.49/1.54  tff(c_484, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36])).
% 3.49/1.54  tff(c_32, plain, (![A_37, B_38]: (m1_connsp_2('#skF_1'(A_37, B_38), A_37, B_38) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.49/1.54  tff(c_553, plain, (![C_178, A_179, B_180]: (m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_connsp_2(C_178, A_179, B_180) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_561, plain, (![A_184, B_185]: (m1_subset_1('#skF_1'(A_184, B_185), k1_zfmisc_1(u1_struct_0(A_184))) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_32, c_553])).
% 3.49/1.54  tff(c_567, plain, (![B_185]: (m1_subset_1('#skF_1'('#skF_2', B_185), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_185, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_561])).
% 3.49/1.54  tff(c_570, plain, (![B_185]: (m1_subset_1('#skF_1'('#skF_2', B_185), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_185, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_72, c_567])).
% 3.49/1.54  tff(c_571, plain, (![B_185]: (m1_subset_1('#skF_1'('#skF_2', B_185), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_185, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_570])).
% 3.49/1.54  tff(c_557, plain, (![C_181, B_182, A_183]: (r2_hidden(C_181, B_182) | ~m1_connsp_2(B_182, A_183, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_183)) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.49/1.54  tff(c_578, plain, (![B_187, A_188]: (r2_hidden(B_187, '#skF_1'(A_188, B_187)) | ~m1_subset_1('#skF_1'(A_188, B_187), k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_187, u1_struct_0(A_188)) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_32, c_557])).
% 3.49/1.54  tff(c_582, plain, (![B_187]: (r2_hidden(B_187, '#skF_1'('#skF_2', B_187)) | ~m1_subset_1('#skF_1'('#skF_2', B_187), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_187, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_578])).
% 3.49/1.54  tff(c_585, plain, (![B_187]: (r2_hidden(B_187, '#skF_1'('#skF_2', B_187)) | ~m1_subset_1('#skF_1'('#skF_2', B_187), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_187, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_72, c_582])).
% 3.49/1.54  tff(c_587, plain, (![B_189]: (r2_hidden(B_189, '#skF_1'('#skF_2', B_189)) | ~m1_subset_1('#skF_1'('#skF_2', B_189), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_189, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_585])).
% 3.49/1.54  tff(c_591, plain, (![B_190]: (r2_hidden(B_190, '#skF_1'('#skF_2', B_190)) | ~m1_subset_1(B_190, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_571, c_587])).
% 3.49/1.54  tff(c_595, plain, (![B_191, A_192]: (r2_hidden(B_191, A_192) | ~m1_subset_1('#skF_1'('#skF_2', B_191), k1_zfmisc_1(A_192)) | ~m1_subset_1(B_191, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_591, c_8])).
% 3.49/1.54  tff(c_603, plain, (![B_185]: (r2_hidden(B_185, k2_struct_0('#skF_2')) | ~m1_subset_1(B_185, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_571, c_595])).
% 3.49/1.54  tff(c_501, plain, (![A_166, B_167]: (k6_domain_1(A_166, B_167)=k1_tarski(B_167) | ~m1_subset_1(B_167, A_166) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.49/1.54  tff(c_513, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_485, c_501])).
% 3.49/1.54  tff(c_514, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_513])).
% 3.49/1.54  tff(c_517, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_514, c_16])).
% 3.49/1.54  tff(c_520, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_517])).
% 3.49/1.54  tff(c_523, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_520])).
% 3.49/1.54  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_523])).
% 3.49/1.54  tff(c_528, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_513])).
% 3.49/1.54  tff(c_482, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 3.49/1.54  tff(c_497, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_482])).
% 3.49/1.54  tff(c_531, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_497])).
% 3.49/1.54  tff(c_644, plain, (![B_206, A_207, C_208]: (r1_tarski(B_206, k1_tops_1(A_207, C_208)) | ~m2_connsp_2(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.49/1.54  tff(c_651, plain, (![B_206, C_208]: (r1_tarski(B_206, k1_tops_1('#skF_2', C_208)) | ~m2_connsp_2(C_208, '#skF_2', B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_644])).
% 3.49/1.54  tff(c_662, plain, (![B_212, C_213]: (r1_tarski(B_212, k1_tops_1('#skF_2', C_213)) | ~m2_connsp_2(C_213, '#skF_2', B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_212, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_72, c_651])).
% 3.49/1.54  tff(c_673, plain, (![B_214]: (r1_tarski(B_214, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_214) | ~m1_subset_1(B_214, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_484, c_662])).
% 3.49/1.54  tff(c_689, plain, (![A_218]: (r1_tarski(k1_tarski(A_218), k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_218)) | ~r2_hidden(A_218, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_673])).
% 3.49/1.54  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | ~r1_tarski(k1_tarski(A_2), B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.54  tff(c_699, plain, (![A_219]: (r2_hidden(A_219, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_219)) | ~r2_hidden(A_219, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_689, c_4])).
% 3.49/1.54  tff(c_703, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_531, c_699])).
% 3.49/1.54  tff(c_704, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_703])).
% 3.49/1.54  tff(c_713, plain, (~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_603, c_704])).
% 3.49/1.54  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_713])).
% 3.49/1.54  tff(c_718, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_703])).
% 3.49/1.54  tff(c_20, plain, (![C_21, A_15, B_19]: (m1_connsp_2(C_21, A_15, B_19) | ~r2_hidden(B_19, k1_tops_1(A_15, C_21)) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, u1_struct_0(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.49/1.54  tff(c_724, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_718, c_20])).
% 3.49/1.54  tff(c_729, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_485, c_72, c_484, c_72, c_724])).
% 3.49/1.54  tff(c_731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_483, c_729])).
% 3.49/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.54  
% 3.49/1.54  Inference rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Ref     : 0
% 3.49/1.54  #Sup     : 136
% 3.49/1.54  #Fact    : 0
% 3.49/1.54  #Define  : 0
% 3.49/1.54  #Split   : 8
% 3.49/1.54  #Chain   : 0
% 3.49/1.54  #Close   : 0
% 3.49/1.54  
% 3.49/1.54  Ordering : KBO
% 3.49/1.54  
% 3.49/1.54  Simplification rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Subsume      : 13
% 3.49/1.54  #Demod        : 143
% 3.49/1.54  #Tautology    : 38
% 3.49/1.54  #SimpNegUnit  : 22
% 3.49/1.54  #BackRed      : 6
% 3.49/1.54  
% 3.49/1.54  #Partial instantiations: 0
% 3.49/1.54  #Strategies tried      : 1
% 3.49/1.54  
% 3.49/1.54  Timing (in seconds)
% 3.49/1.54  ----------------------
% 3.49/1.54  Preprocessing        : 0.35
% 3.49/1.54  Parsing              : 0.19
% 3.49/1.54  CNF conversion       : 0.03
% 3.49/1.54  Main loop            : 0.41
% 3.49/1.54  Inferencing          : 0.16
% 3.49/1.54  Reduction            : 0.12
% 3.49/1.54  Demodulation         : 0.08
% 3.49/1.54  BG Simplification    : 0.02
% 3.49/1.54  Subsumption          : 0.07
% 3.49/1.54  Abstraction          : 0.02
% 3.49/1.54  MUC search           : 0.00
% 3.49/1.54  Cooper               : 0.00
% 3.49/1.54  Total                : 0.81
% 3.49/1.54  Index Insertion      : 0.00
% 3.49/1.54  Index Deletion       : 0.00
% 3.49/1.54  Index Matching       : 0.00
% 3.49/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
