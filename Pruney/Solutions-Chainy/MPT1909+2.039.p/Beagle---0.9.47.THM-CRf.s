%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 183 expanded)
%              Number of leaves         :   40 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  213 ( 841 expanded)
%              Number of equality atoms :   33 ( 122 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( m1_subset_1(k1_tarski(B_5),k1_zfmisc_1(A_4))
      | k1_xboole_0 = A_4
      | ~ m1_subset_1(B_5,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(B_92)))
      | ~ m1_pre_topc(B_92,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_167,plain,(
    ! [B_95,A_96,B_97] :
      ( m1_subset_1(k1_tarski(B_95),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96)
      | u1_struct_0(B_97) = k1_xboole_0
      | ~ m1_subset_1(B_95,u1_struct_0(B_97)) ) ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_169,plain,(
    ! [B_95] :
      ( m1_subset_1(k1_tarski(B_95),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_167])).

tff(c_172,plain,(
    ! [B_95] :
      ( m1_subset_1(k1_tarski(B_95),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_169])).

tff(c_173,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_69,plain,(
    ! [B_79,A_80] :
      ( l1_pre_topc(B_79)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_75,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_72])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_86,plain,(
    ! [A_84,B_85] :
      ( k6_domain_1(A_84,B_85) = k1_tarski(B_85)
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_97,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_99,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_14])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_102])).

tff(c_113,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_113])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_177,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_119])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_185,plain,(
    u1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_42,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_34,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_30,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_191,plain,(
    ! [B_102] :
      ( m1_subset_1(k1_tarski(B_102),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_20,plain,(
    ! [A_20,B_36,C_44,E_50] :
      ( k8_relset_1(u1_struct_0(A_20),u1_struct_0(B_36),C_44,E_50) = k2_pre_topc(A_20,E_50)
      | ~ m1_subset_1(E_50,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(E_50,k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ v3_borsuk_1(C_44,A_20,B_36)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20),u1_struct_0(B_36))))
      | ~ v5_pre_topc(C_44,A_20,B_36)
      | ~ v1_funct_2(C_44,u1_struct_0(A_20),u1_struct_0(B_36))
      | ~ v1_funct_1(C_44)
      | ~ m1_pre_topc(B_36,A_20)
      | ~ v4_tex_2(B_36,A_20)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_20)
      | ~ v3_tdlat_3(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_193,plain,(
    ! [B_36,C_44,B_102] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_36),C_44,k1_tarski(B_102)) = k2_pre_topc('#skF_1',k1_tarski(B_102))
      | ~ m1_subset_1(k1_tarski(B_102),k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ v3_borsuk_1(C_44,'#skF_1',B_36)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_36))))
      | ~ v5_pre_topc(C_44,'#skF_1',B_36)
      | ~ v1_funct_2(C_44,u1_struct_0('#skF_1'),u1_struct_0(B_36))
      | ~ v1_funct_1(C_44)
      | ~ m1_pre_topc(B_36,'#skF_1')
      | ~ v4_tex_2(B_36,'#skF_1')
      | v2_struct_0(B_36)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_191,c_20])).

tff(c_201,plain,(
    ! [B_36,C_44,B_102] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_36),C_44,k1_tarski(B_102)) = k2_pre_topc('#skF_1',k1_tarski(B_102))
      | ~ m1_subset_1(k1_tarski(B_102),k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ v3_borsuk_1(C_44,'#skF_1',B_36)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_36))))
      | ~ v5_pre_topc(C_44,'#skF_1',B_36)
      | ~ v1_funct_2(C_44,u1_struct_0('#skF_1'),u1_struct_0(B_36))
      | ~ v1_funct_1(C_44)
      | ~ m1_pre_topc(B_36,'#skF_1')
      | ~ v4_tex_2(B_36,'#skF_1')
      | v2_struct_0(B_36)
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_193])).

tff(c_217,plain,(
    ! [B_105,C_106,B_107] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_105),C_106,k1_tarski(B_107)) = k2_pre_topc('#skF_1',k1_tarski(B_107))
      | ~ m1_subset_1(k1_tarski(B_107),k1_zfmisc_1(u1_struct_0(B_105)))
      | ~ v3_borsuk_1(C_106,'#skF_1',B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_105))))
      | ~ v5_pre_topc(C_106,'#skF_1',B_105)
      | ~ v1_funct_2(C_106,u1_struct_0('#skF_1'),u1_struct_0(B_105))
      | ~ v1_funct_1(C_106)
      | ~ m1_pre_topc(B_105,'#skF_1')
      | ~ v4_tex_2(B_105,'#skF_1')
      | v2_struct_0(B_105)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_201])).

tff(c_285,plain,(
    ! [B_123,C_124,B_125] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_123),C_124,k1_tarski(B_125)) = k2_pre_topc('#skF_1',k1_tarski(B_125))
      | ~ v3_borsuk_1(C_124,'#skF_1',B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_123))))
      | ~ v5_pre_topc(C_124,'#skF_1',B_123)
      | ~ v1_funct_2(C_124,u1_struct_0('#skF_1'),u1_struct_0(B_123))
      | ~ v1_funct_1(C_124)
      | ~ m1_pre_topc(B_123,'#skF_1')
      | ~ v4_tex_2(B_123,'#skF_1')
      | v2_struct_0(B_123)
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_2'))
      | u1_struct_0(B_123) = k1_xboole_0
      | ~ m1_subset_1(B_125,u1_struct_0(B_123)) ) ),
    inference(resolution,[status(thm)],[c_8,c_217])).

tff(c_290,plain,(
    ! [B_125] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(B_125)) = k2_pre_topc('#skF_1',k1_tarski(B_125))
      | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_285])).

tff(c_294,plain,(
    ! [B_125] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(B_125)) = k2_pre_topc('#skF_1',k1_tarski(B_125))
      | v2_struct_0('#skF_2')
      | u1_struct_0('#skF_2') = k1_xboole_0
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_30,c_290])).

tff(c_296,plain,(
    ! [B_126] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(B_126)) = k2_pre_topc('#skF_1',k1_tarski(B_126))
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_44,c_294])).

tff(c_24,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_53,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_98,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_53,c_86])).

tff(c_125,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_128,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_14])).

tff(c_131,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_128])).

tff(c_134,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_134])).

tff(c_139,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_118,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_22,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_124,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_54])).

tff(c_141,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_124])).

tff(c_302,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_141])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.45  
% 2.62/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.45  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.62/1.45  
% 2.62/1.45  %Foreground sorts:
% 2.62/1.45  
% 2.62/1.45  
% 2.62/1.45  %Background operators:
% 2.62/1.45  
% 2.62/1.45  
% 2.62/1.45  %Foreground operators:
% 2.62/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.62/1.45  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.62/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.45  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.62/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.62/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.62/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.62/1.45  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.62/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.45  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.62/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.62/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.62/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.62/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.45  
% 3.05/1.49  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.05/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.05/1.49  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 3.05/1.49  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.05/1.49  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.05/1.49  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.05/1.49  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.05/1.49  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.05/1.49  tff(f_111, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.05/1.49  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.05/1.49  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_8, plain, (![B_5, A_4]: (m1_subset_1(k1_tarski(B_5), k1_zfmisc_1(A_4)) | k1_xboole_0=A_4 | ~m1_subset_1(B_5, A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.49  tff(c_151, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(B_92))) | ~m1_pre_topc(B_92, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.49  tff(c_167, plain, (![B_95, A_96, B_97]: (m1_subset_1(k1_tarski(B_95), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96) | u1_struct_0(B_97)=k1_xboole_0 | ~m1_subset_1(B_95, u1_struct_0(B_97)))), inference(resolution, [status(thm)], [c_8, c_151])).
% 3.05/1.49  tff(c_169, plain, (![B_95]: (m1_subset_1(k1_tarski(B_95), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_95, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_167])).
% 3.05/1.49  tff(c_172, plain, (![B_95]: (m1_subset_1(k1_tarski(B_95), k1_zfmisc_1(u1_struct_0('#skF_1'))) | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_95, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_169])).
% 3.05/1.49  tff(c_173, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 3.05/1.49  tff(c_69, plain, (![B_79, A_80]: (l1_pre_topc(B_79) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.05/1.49  tff(c_72, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_69])).
% 3.05/1.49  tff(c_75, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_72])).
% 3.05/1.49  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.49  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_86, plain, (![A_84, B_85]: (k6_domain_1(A_84, B_85)=k1_tarski(B_85) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.05/1.49  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_86])).
% 3.05/1.49  tff(c_99, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_97])).
% 3.05/1.49  tff(c_14, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.05/1.49  tff(c_102, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_99, c_14])).
% 3.05/1.49  tff(c_105, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_102])).
% 3.05/1.49  tff(c_113, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_105])).
% 3.05/1.49  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_113])).
% 3.05/1.49  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_97])).
% 3.05/1.49  tff(c_177, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_119])).
% 3.05/1.49  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_177])).
% 3.05/1.49  tff(c_185, plain, (u1_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_172])).
% 3.05/1.49  tff(c_42, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_34, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_30, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_48, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_191, plain, (![B_102]: (m1_subset_1(k1_tarski(B_102), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_102, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_172])).
% 3.05/1.49  tff(c_20, plain, (![A_20, B_36, C_44, E_50]: (k8_relset_1(u1_struct_0(A_20), u1_struct_0(B_36), C_44, E_50)=k2_pre_topc(A_20, E_50) | ~m1_subset_1(E_50, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(E_50, k1_zfmisc_1(u1_struct_0(B_36))) | ~v3_borsuk_1(C_44, A_20, B_36) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20), u1_struct_0(B_36)))) | ~v5_pre_topc(C_44, A_20, B_36) | ~v1_funct_2(C_44, u1_struct_0(A_20), u1_struct_0(B_36)) | ~v1_funct_1(C_44) | ~m1_pre_topc(B_36, A_20) | ~v4_tex_2(B_36, A_20) | v2_struct_0(B_36) | ~l1_pre_topc(A_20) | ~v3_tdlat_3(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.05/1.49  tff(c_193, plain, (![B_36, C_44, B_102]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_36), C_44, k1_tarski(B_102))=k2_pre_topc('#skF_1', k1_tarski(B_102)) | ~m1_subset_1(k1_tarski(B_102), k1_zfmisc_1(u1_struct_0(B_36))) | ~v3_borsuk_1(C_44, '#skF_1', B_36) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_36)))) | ~v5_pre_topc(C_44, '#skF_1', B_36) | ~v1_funct_2(C_44, u1_struct_0('#skF_1'), u1_struct_0(B_36)) | ~v1_funct_1(C_44) | ~m1_pre_topc(B_36, '#skF_1') | ~v4_tex_2(B_36, '#skF_1') | v2_struct_0(B_36) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(B_102, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_191, c_20])).
% 3.05/1.49  tff(c_201, plain, (![B_36, C_44, B_102]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_36), C_44, k1_tarski(B_102))=k2_pre_topc('#skF_1', k1_tarski(B_102)) | ~m1_subset_1(k1_tarski(B_102), k1_zfmisc_1(u1_struct_0(B_36))) | ~v3_borsuk_1(C_44, '#skF_1', B_36) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_36)))) | ~v5_pre_topc(C_44, '#skF_1', B_36) | ~v1_funct_2(C_44, u1_struct_0('#skF_1'), u1_struct_0(B_36)) | ~v1_funct_1(C_44) | ~m1_pre_topc(B_36, '#skF_1') | ~v4_tex_2(B_36, '#skF_1') | v2_struct_0(B_36) | v2_struct_0('#skF_1') | ~m1_subset_1(B_102, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_193])).
% 3.05/1.49  tff(c_217, plain, (![B_105, C_106, B_107]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_105), C_106, k1_tarski(B_107))=k2_pre_topc('#skF_1', k1_tarski(B_107)) | ~m1_subset_1(k1_tarski(B_107), k1_zfmisc_1(u1_struct_0(B_105))) | ~v3_borsuk_1(C_106, '#skF_1', B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_105)))) | ~v5_pre_topc(C_106, '#skF_1', B_105) | ~v1_funct_2(C_106, u1_struct_0('#skF_1'), u1_struct_0(B_105)) | ~v1_funct_1(C_106) | ~m1_pre_topc(B_105, '#skF_1') | ~v4_tex_2(B_105, '#skF_1') | v2_struct_0(B_105) | ~m1_subset_1(B_107, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_201])).
% 3.05/1.49  tff(c_285, plain, (![B_123, C_124, B_125]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_123), C_124, k1_tarski(B_125))=k2_pre_topc('#skF_1', k1_tarski(B_125)) | ~v3_borsuk_1(C_124, '#skF_1', B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_123)))) | ~v5_pre_topc(C_124, '#skF_1', B_123) | ~v1_funct_2(C_124, u1_struct_0('#skF_1'), u1_struct_0(B_123)) | ~v1_funct_1(C_124) | ~m1_pre_topc(B_123, '#skF_1') | ~v4_tex_2(B_123, '#skF_1') | v2_struct_0(B_123) | ~m1_subset_1(B_125, u1_struct_0('#skF_2')) | u1_struct_0(B_123)=k1_xboole_0 | ~m1_subset_1(B_125, u1_struct_0(B_123)))), inference(resolution, [status(thm)], [c_8, c_217])).
% 3.05/1.49  tff(c_290, plain, (![B_125]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(B_125))=k2_pre_topc('#skF_1', k1_tarski(B_125)) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_125, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_285])).
% 3.05/1.49  tff(c_294, plain, (![B_125]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(B_125))=k2_pre_topc('#skF_1', k1_tarski(B_125)) | v2_struct_0('#skF_2') | u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_subset_1(B_125, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_30, c_290])).
% 3.05/1.49  tff(c_296, plain, (![B_126]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(B_126))=k2_pre_topc('#skF_1', k1_tarski(B_126)) | ~m1_subset_1(B_126, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_185, c_44, c_294])).
% 3.05/1.49  tff(c_24, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_53, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.05/1.49  tff(c_98, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_53, c_86])).
% 3.05/1.49  tff(c_125, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.05/1.49  tff(c_128, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_125, c_14])).
% 3.05/1.49  tff(c_131, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_128])).
% 3.05/1.49  tff(c_134, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_131])).
% 3.05/1.49  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_134])).
% 3.05/1.49  tff(c_139, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 3.05/1.49  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_97])).
% 3.05/1.49  tff(c_22, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.05/1.49  tff(c_54, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 3.05/1.49  tff(c_124, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_54])).
% 3.05/1.49  tff(c_141, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_124])).
% 3.05/1.49  tff(c_302, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_141])).
% 3.05/1.49  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_302])).
% 3.05/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  Inference rules
% 3.05/1.49  ----------------------
% 3.05/1.49  #Ref     : 0
% 3.05/1.49  #Sup     : 50
% 3.05/1.49  #Fact    : 0
% 3.05/1.49  #Define  : 0
% 3.05/1.49  #Split   : 7
% 3.05/1.49  #Chain   : 0
% 3.05/1.49  #Close   : 0
% 3.05/1.49  
% 3.05/1.49  Ordering : KBO
% 3.05/1.49  
% 3.05/1.49  Simplification rules
% 3.05/1.49  ----------------------
% 3.05/1.49  #Subsume      : 1
% 3.05/1.49  #Demod        : 35
% 3.05/1.49  #Tautology    : 17
% 3.05/1.49  #SimpNegUnit  : 7
% 3.05/1.49  #BackRed      : 8
% 3.05/1.49  
% 3.05/1.49  #Partial instantiations: 0
% 3.05/1.49  #Strategies tried      : 1
% 3.05/1.49  
% 3.05/1.49  Timing (in seconds)
% 3.05/1.49  ----------------------
% 3.18/1.49  Preprocessing        : 0.36
% 3.18/1.49  Parsing              : 0.19
% 3.18/1.49  CNF conversion       : 0.03
% 3.18/1.49  Main loop            : 0.28
% 3.18/1.49  Inferencing          : 0.10
% 3.18/1.49  Reduction            : 0.09
% 3.18/1.49  Demodulation         : 0.06
% 3.18/1.49  BG Simplification    : 0.02
% 3.18/1.49  Subsumption          : 0.06
% 3.18/1.49  Abstraction          : 0.01
% 3.18/1.49  MUC search           : 0.00
% 3.18/1.49  Cooper               : 0.00
% 3.18/1.49  Total                : 0.71
% 3.18/1.49  Index Insertion      : 0.00
% 3.18/1.49  Index Deletion       : 0.00
% 3.18/1.49  Index Matching       : 0.00
% 3.18/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
