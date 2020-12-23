%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 137 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  205 ( 534 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    ! [A_14,B_22] :
      ( m1_subset_1('#skF_2'(A_14,B_22),u1_struct_0(A_14))
      | v2_tex_2(B_22,A_14)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_106,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_2'(A_56,B_57),B_57)
      | v2_tex_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_115,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_106])).

tff(c_121,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_115])).

tff(c_122,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_121])).

tff(c_37,plain,(
    ! [C_33,B_34,A_35] :
      ( ~ v1_xboole_0(C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_41,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k6_domain_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ! [A_46,B_47] :
      ( v4_pre_topc(k2_pre_topc(A_46,B_47),A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [A_46,B_7] :
      ( v4_pre_topc(k2_pre_topc(A_46,k6_domain_1(u1_struct_0(A_46),B_7)),A_46)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | ~ m1_subset_1(B_7,u1_struct_0(A_46))
      | v1_xboole_0(u1_struct_0(A_46)) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,(
    ! [B_49,A_50] :
      ( v3_pre_topc(B_49,A_50)
      | ~ v4_pre_topc(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v3_tdlat_3(A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_137,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k2_pre_topc(A_67,B_68),A_67)
      | ~ v4_pre_topc(k2_pre_topc(A_67,B_68),A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_188,plain,(
    ! [A_83,B_84] :
      ( v3_pre_topc(k2_pre_topc(A_83,k6_domain_1(u1_struct_0(A_83),B_84)),A_83)
      | ~ v3_tdlat_3(A_83)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_83),B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | ~ m1_subset_1(B_84,u1_struct_0(A_83))
      | v1_xboole_0(u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_78,c_137])).

tff(c_192,plain,(
    ! [A_83,B_7] :
      ( v3_pre_topc(k2_pre_topc(A_83,k6_domain_1(u1_struct_0(A_83),B_7)),A_83)
      | ~ v3_tdlat_3(A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | ~ m1_subset_1(B_7,u1_struct_0(A_83))
      | v1_xboole_0(u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_26,plain,(
    ! [C_32] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_32))) = k6_domain_1(u1_struct_0('#skF_3'),C_32)
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_130,plain,(
    ! [A_63,B_64,D_65] :
      ( k9_subset_1(u1_struct_0(A_63),B_64,D_65) != k6_domain_1(u1_struct_0(A_63),'#skF_2'(A_63,B_64))
      | ~ v3_pre_topc(D_65,A_63)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_132,plain,(
    ! [C_32] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_32) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_32)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_32)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_130])).

tff(c_134,plain,(
    ! [C_32] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_32) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_32)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_32)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_132])).

tff(c_180,plain,(
    ! [C_80] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_80) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_80)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_80)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_80,'#skF_4')
      | ~ m1_subset_1(C_80,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_134])).

tff(c_183,plain,(
    ! [C_80] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_80) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_80)),'#skF_3')
      | ~ r2_hidden(C_80,'#skF_4')
      | ~ m1_subset_1(C_80,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_80),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_195,plain,(
    ! [C_89] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_89) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_89)),'#skF_3')
      | ~ r2_hidden(C_89,'#skF_4')
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_89),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_183])).

tff(c_199,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_7) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_7)),'#skF_3')
      | ~ r2_hidden(B_7,'#skF_4')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_203,plain,(
    ! [B_90] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_90) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_90)),'#skF_3')
      | ~ r2_hidden(B_90,'#skF_4')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_199])).

tff(c_207,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_7) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_7,'#skF_4')
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_192,c_203])).

tff(c_210,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_7) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_7,'#skF_4')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_32,c_207])).

tff(c_211,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_7) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_7,'#skF_4')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_210])).

tff(c_214,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_211])).

tff(c_216,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_214])).

tff(c_220,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_216])).

tff(c_223,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_220])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_223])).

tff(c_226,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_284,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_2'(A_112,B_113),B_113)
      | v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_293,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_284])).

tff(c_299,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_293])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_226,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.38  
% 2.64/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.39  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.64/1.39  
% 2.64/1.39  %Foreground sorts:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Background operators:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Foreground operators:
% 2.64/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.64/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.64/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.39  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.64/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.64/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.64/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.64/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.39  
% 2.64/1.40  tff(f_114, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 2.64/1.40  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 2.64/1.40  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.64/1.40  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.64/1.40  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.64/1.40  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.64/1.40  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.64/1.40  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_24, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_22, plain, (![A_14, B_22]: (m1_subset_1('#skF_2'(A_14, B_22), u1_struct_0(A_14)) | v2_tex_2(B_22, A_14) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.40  tff(c_106, plain, (![A_56, B_57]: (r2_hidden('#skF_2'(A_56, B_57), B_57) | v2_tex_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.40  tff(c_115, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_106])).
% 2.64/1.40  tff(c_121, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_115])).
% 2.64/1.40  tff(c_122, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_121])).
% 2.64/1.40  tff(c_37, plain, (![C_33, B_34, A_35]: (~v1_xboole_0(C_33) | ~m1_subset_1(B_34, k1_zfmisc_1(C_33)) | ~r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.40  tff(c_40, plain, (![A_35]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_35, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_37])).
% 2.64/1.40  tff(c_41, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.64/1.40  tff(c_32, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k6_domain_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.40  tff(c_66, plain, (![A_46, B_47]: (v4_pre_topc(k2_pre_topc(A_46, B_47), A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.64/1.40  tff(c_78, plain, (![A_46, B_7]: (v4_pre_topc(k2_pre_topc(A_46, k6_domain_1(u1_struct_0(A_46), B_7)), A_46) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | ~m1_subset_1(B_7, u1_struct_0(A_46)) | v1_xboole_0(u1_struct_0(A_46)))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.64/1.40  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k2_pre_topc(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.40  tff(c_83, plain, (![B_49, A_50]: (v3_pre_topc(B_49, A_50) | ~v4_pre_topc(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~v3_tdlat_3(A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.40  tff(c_137, plain, (![A_67, B_68]: (v3_pre_topc(k2_pre_topc(A_67, B_68), A_67) | ~v4_pre_topc(k2_pre_topc(A_67, B_68), A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.64/1.40  tff(c_188, plain, (![A_83, B_84]: (v3_pre_topc(k2_pre_topc(A_83, k6_domain_1(u1_struct_0(A_83), B_84)), A_83) | ~v3_tdlat_3(A_83) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_83), B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | ~m1_subset_1(B_84, u1_struct_0(A_83)) | v1_xboole_0(u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_78, c_137])).
% 2.64/1.40  tff(c_192, plain, (![A_83, B_7]: (v3_pre_topc(k2_pre_topc(A_83, k6_domain_1(u1_struct_0(A_83), B_7)), A_83) | ~v3_tdlat_3(A_83) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | ~m1_subset_1(B_7, u1_struct_0(A_83)) | v1_xboole_0(u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_6, c_188])).
% 2.64/1.40  tff(c_26, plain, (![C_32]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_32)))=k6_domain_1(u1_struct_0('#skF_3'), C_32) | ~r2_hidden(C_32, '#skF_4') | ~m1_subset_1(C_32, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_130, plain, (![A_63, B_64, D_65]: (k9_subset_1(u1_struct_0(A_63), B_64, D_65)!=k6_domain_1(u1_struct_0(A_63), '#skF_2'(A_63, B_64)) | ~v3_pre_topc(D_65, A_63) | ~m1_subset_1(D_65, k1_zfmisc_1(u1_struct_0(A_63))) | v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.40  tff(c_132, plain, (![C_32]: (k6_domain_1(u1_struct_0('#skF_3'), C_32)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_32)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_32)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_32, '#skF_4') | ~m1_subset_1(C_32, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_130])).
% 2.64/1.40  tff(c_134, plain, (![C_32]: (k6_domain_1(u1_struct_0('#skF_3'), C_32)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_32)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_32)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_32, '#skF_4') | ~m1_subset_1(C_32, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_132])).
% 2.64/1.40  tff(c_180, plain, (![C_80]: (k6_domain_1(u1_struct_0('#skF_3'), C_80)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_80)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_80)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_80, '#skF_4') | ~m1_subset_1(C_80, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_134])).
% 2.64/1.40  tff(c_183, plain, (![C_80]: (k6_domain_1(u1_struct_0('#skF_3'), C_80)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_80)), '#skF_3') | ~r2_hidden(C_80, '#skF_4') | ~m1_subset_1(C_80, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_80), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_180])).
% 2.64/1.40  tff(c_195, plain, (![C_89]: (k6_domain_1(u1_struct_0('#skF_3'), C_89)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_89)), '#skF_3') | ~r2_hidden(C_89, '#skF_4') | ~m1_subset_1(C_89, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_89), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_183])).
% 2.64/1.40  tff(c_199, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_3'), B_7)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_7)), '#skF_3') | ~r2_hidden(B_7, '#skF_4') | ~m1_subset_1(B_7, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_195])).
% 2.64/1.40  tff(c_203, plain, (![B_90]: (k6_domain_1(u1_struct_0('#skF_3'), B_90)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_90)), '#skF_3') | ~r2_hidden(B_90, '#skF_4') | ~m1_subset_1(B_90, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_41, c_199])).
% 2.64/1.40  tff(c_207, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_3'), B_7)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_7, '#skF_4') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_192, c_203])).
% 2.64/1.40  tff(c_210, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_3'), B_7)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_7, '#skF_4') | ~m1_subset_1(B_7, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_32, c_207])).
% 2.64/1.40  tff(c_211, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_3'), B_7)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_7, '#skF_4') | ~m1_subset_1(B_7, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_41, c_210])).
% 2.64/1.40  tff(c_214, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_211])).
% 2.64/1.40  tff(c_216, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_214])).
% 2.64/1.40  tff(c_220, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_216])).
% 2.64/1.40  tff(c_223, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_220])).
% 2.64/1.40  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_223])).
% 2.64/1.40  tff(c_226, plain, (![A_35]: (~r2_hidden(A_35, '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 2.64/1.40  tff(c_284, plain, (![A_112, B_113]: (r2_hidden('#skF_2'(A_112, B_113), B_113) | v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.40  tff(c_293, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_284])).
% 2.64/1.40  tff(c_299, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_293])).
% 2.64/1.40  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_226, c_299])).
% 2.64/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.40  
% 2.64/1.40  Inference rules
% 2.64/1.40  ----------------------
% 2.64/1.40  #Ref     : 1
% 2.64/1.40  #Sup     : 50
% 2.64/1.40  #Fact    : 0
% 2.64/1.40  #Define  : 0
% 2.64/1.40  #Split   : 3
% 2.64/1.40  #Chain   : 0
% 2.64/1.40  #Close   : 0
% 2.64/1.40  
% 2.64/1.40  Ordering : KBO
% 2.64/1.40  
% 2.64/1.40  Simplification rules
% 2.64/1.40  ----------------------
% 2.64/1.40  #Subsume      : 7
% 2.64/1.40  #Demod        : 31
% 2.64/1.40  #Tautology    : 8
% 2.64/1.40  #SimpNegUnit  : 7
% 2.64/1.40  #BackRed      : 0
% 2.64/1.40  
% 2.64/1.40  #Partial instantiations: 0
% 2.64/1.40  #Strategies tried      : 1
% 2.64/1.40  
% 2.64/1.40  Timing (in seconds)
% 2.64/1.40  ----------------------
% 2.64/1.41  Preprocessing        : 0.32
% 2.64/1.41  Parsing              : 0.18
% 2.64/1.41  CNF conversion       : 0.02
% 2.64/1.41  Main loop            : 0.26
% 2.64/1.41  Inferencing          : 0.12
% 2.64/1.41  Reduction            : 0.07
% 2.64/1.41  Demodulation         : 0.05
% 2.64/1.41  BG Simplification    : 0.02
% 2.64/1.41  Subsumption          : 0.04
% 2.64/1.41  Abstraction          : 0.01
% 2.64/1.41  MUC search           : 0.00
% 2.64/1.41  Cooper               : 0.00
% 2.64/1.41  Total                : 0.61
% 2.64/1.41  Index Insertion      : 0.00
% 2.64/1.41  Index Deletion       : 0.00
% 2.64/1.41  Index Matching       : 0.00
% 2.64/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
