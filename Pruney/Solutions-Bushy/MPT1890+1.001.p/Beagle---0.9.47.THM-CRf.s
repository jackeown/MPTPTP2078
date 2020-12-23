%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:38 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 132 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  182 ( 532 expanded)
%              Number of equality atoms :   14 (  47 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14,plain,(
    ! [A_10,B_18] :
      ( m1_subset_1('#skF_1'(A_10,B_18),u1_struct_0(A_10))
      | v2_tex_2(B_18,A_10)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v3_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_80,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_56)
      | v2_tex_2(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v3_tdlat_3(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_92,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_87])).

tff(c_93,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_92])).

tff(c_31,plain,(
    ! [C_32,B_33,A_34] :
      ( ~ v1_xboole_0(C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_31])).

tff(c_35,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k6_domain_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_47,B_48] :
      ( v4_pre_topc(k2_pre_topc(A_47,B_48),A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_47,B_4] :
      ( v4_pre_topc(k2_pre_topc(A_47,k6_domain_1(u1_struct_0(A_47),B_4)),A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_subset_1(B_4,u1_struct_0(A_47))
      | v1_xboole_0(u1_struct_0(A_47)) ) ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k2_pre_topc(A_1,B_2),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    ! [C_31] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31))) = k6_domain_1(u1_struct_0('#skF_2'),C_31)
      | ~ r2_hidden(C_31,'#skF_3')
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_104,plain,(
    ! [A_65,B_66,D_67] :
      ( k9_subset_1(u1_struct_0(A_65),B_66,D_67) != k6_domain_1(u1_struct_0(A_65),'#skF_1'(A_65,B_66))
      | ~ v4_pre_topc(D_67,A_65)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(u1_struct_0(A_65)))
      | v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v3_tdlat_3(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_106,plain,(
    ! [C_31] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_31) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_31,'#skF_3')
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_108,plain,(
    ! [C_31] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_31) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_31,'#skF_3')
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_106])).

tff(c_126,plain,(
    ! [C_74] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_74) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_74)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_74)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_74,'#skF_3')
      | ~ m1_subset_1(C_74,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_108])).

tff(c_129,plain,(
    ! [C_74] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_74) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_74)),'#skF_2')
      | ~ r2_hidden(C_74,'#skF_3')
      | ~ m1_subset_1(C_74,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_74),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2,c_126])).

tff(c_139,plain,(
    ! [C_79] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_79) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_79)),'#skF_2')
      | ~ r2_hidden(C_79,'#skF_3')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_79),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_129])).

tff(c_143,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_4)),'#skF_2')
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4,c_139])).

tff(c_147,plain,(
    ! [B_80] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_80) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_80)),'#skF_2')
      | ~ r2_hidden(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_143])).

tff(c_151,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_74,c_147])).

tff(c_154,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_151])).

tff(c_155,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_154])).

tff(c_158,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_155])).

tff(c_160,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_158])).

tff(c_164,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_160])).

tff(c_170,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_164])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_170])).

tff(c_173,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_208,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_96)
      | v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v3_tdlat_3(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_215,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_208])).

tff(c_220,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_215])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_173,c_220])).

%------------------------------------------------------------------------------
