%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
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

tff(f_103,negated_conjecture,(
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

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

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

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14,plain,(
    ! [A_10,B_18] :
      ( m1_subset_1('#skF_1'(A_10,B_18),u1_struct_0(A_10))
      | v2_tex_2(B_18,A_10)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v3_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_65,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_43)
      | v2_tex_2(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v3_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_77,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_72])).

tff(c_78,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_77])).

tff(c_29,plain,(
    ! [C_29,B_30,A_31] :
      ( ~ v1_xboole_0(C_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_29))
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_33,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k6_domain_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_35,B_36] :
      ( v4_pre_topc(k2_pre_topc(A_35,B_36),A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [A_35,B_7] :
      ( v4_pre_topc(k2_pre_topc(A_35,k6_domain_1(u1_struct_0(A_35),B_7)),A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | ~ m1_subset_1(B_7,u1_struct_0(A_35))
      | v1_xboole_0(u1_struct_0(A_35)) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [C_28] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_28))) = k6_domain_1(u1_struct_0('#skF_2'),C_28)
      | ~ r2_hidden(C_28,'#skF_3')
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_102,plain,(
    ! [A_58,B_59,D_60] :
      ( k9_subset_1(u1_struct_0(A_58),B_59,D_60) != k6_domain_1(u1_struct_0(A_58),'#skF_1'(A_58,B_59))
      | ~ v4_pre_topc(D_60,A_58)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | v2_tex_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v3_tdlat_3(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_104,plain,(
    ! [C_28] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_28) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_28)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_28)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_28,'#skF_3')
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_106,plain,(
    ! [C_28] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_28) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_28)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_28)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_28,'#skF_3')
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_104])).

tff(c_108,plain,(
    ! [C_61] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_61) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_61)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_61)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_61,'#skF_3')
      | ~ m1_subset_1(C_61,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_106])).

tff(c_111,plain,(
    ! [C_61] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_61) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_61)),'#skF_2')
      | ~ r2_hidden(C_61,'#skF_3')
      | ~ m1_subset_1(C_61,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_61),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_115,plain,(
    ! [C_62] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_62) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_62)),'#skF_2')
      | ~ r2_hidden(C_62,'#skF_3')
      | ~ m1_subset_1(C_62,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_62),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_119,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_7)),'#skF_2')
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_123,plain,(
    ! [B_63] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_63) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_63)),'#skF_2')
      | ~ r2_hidden(B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_119])).

tff(c_127,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_53,c_123])).

tff(c_130,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_127])).

tff(c_131,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_130])).

tff(c_134,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_131])).

tff(c_136,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_134])).

tff(c_140,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_136])).

tff(c_143,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_140])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_143])).

tff(c_146,plain,(
    ! [A_31] : ~ r2_hidden(A_31,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_172,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77,B_78),B_78)
      | v2_tex_2(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v3_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_179,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_184,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_179])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_146,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.34  
% 2.22/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.34  %$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.34  
% 2.22/1.34  %Foreground sorts:
% 2.22/1.34  
% 2.22/1.34  
% 2.22/1.34  %Background operators:
% 2.22/1.34  
% 2.22/1.34  
% 2.22/1.34  %Foreground operators:
% 2.22/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.22/1.34  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.22/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.34  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.22/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.22/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.22/1.34  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.22/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.34  
% 2.22/1.35  tff(f_103, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 2.22/1.35  tff(f_81, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 2.22/1.35  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.22/1.35  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.22/1.35  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.22/1.35  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.22/1.35  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_16, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_24, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_14, plain, (![A_10, B_18]: (m1_subset_1('#skF_1'(A_10, B_18), u1_struct_0(A_10)) | v2_tex_2(B_18, A_10) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | ~v3_tdlat_3(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.22/1.35  tff(c_65, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), B_43) | v2_tex_2(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v3_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.22/1.35  tff(c_72, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.22/1.35  tff(c_77, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_72])).
% 2.22/1.35  tff(c_78, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_77])).
% 2.22/1.35  tff(c_29, plain, (![C_29, B_30, A_31]: (~v1_xboole_0(C_29) | ~m1_subset_1(B_30, k1_zfmisc_1(C_29)) | ~r2_hidden(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.35  tff(c_32, plain, (![A_31]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_31, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_29])).
% 2.22/1.35  tff(c_33, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.22/1.35  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k6_domain_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.35  tff(c_47, plain, (![A_35, B_36]: (v4_pre_topc(k2_pre_topc(A_35, B_36), A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.35  tff(c_53, plain, (![A_35, B_7]: (v4_pre_topc(k2_pre_topc(A_35, k6_domain_1(u1_struct_0(A_35), B_7)), A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | ~m1_subset_1(B_7, u1_struct_0(A_35)) | v1_xboole_0(u1_struct_0(A_35)))), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.22/1.35  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k2_pre_topc(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.35  tff(c_18, plain, (![C_28]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_28)))=k6_domain_1(u1_struct_0('#skF_2'), C_28) | ~r2_hidden(C_28, '#skF_3') | ~m1_subset_1(C_28, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.22/1.35  tff(c_102, plain, (![A_58, B_59, D_60]: (k9_subset_1(u1_struct_0(A_58), B_59, D_60)!=k6_domain_1(u1_struct_0(A_58), '#skF_1'(A_58, B_59)) | ~v4_pre_topc(D_60, A_58) | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0(A_58))) | v2_tex_2(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v3_tdlat_3(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.22/1.35  tff(c_104, plain, (![C_28]: (k6_domain_1(u1_struct_0('#skF_2'), C_28)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_28)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_28)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(C_28, '#skF_3') | ~m1_subset_1(C_28, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_102])).
% 2.22/1.35  tff(c_106, plain, (![C_28]: (k6_domain_1(u1_struct_0('#skF_2'), C_28)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_28)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_28)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(C_28, '#skF_3') | ~m1_subset_1(C_28, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_104])).
% 2.22/1.35  tff(c_108, plain, (![C_61]: (k6_domain_1(u1_struct_0('#skF_2'), C_61)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_61)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_61)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_61, '#skF_3') | ~m1_subset_1(C_61, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_106])).
% 2.22/1.35  tff(c_111, plain, (![C_61]: (k6_domain_1(u1_struct_0('#skF_2'), C_61)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_61)), '#skF_2') | ~r2_hidden(C_61, '#skF_3') | ~m1_subset_1(C_61, u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), C_61), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_108])).
% 2.22/1.35  tff(c_115, plain, (![C_62]: (k6_domain_1(u1_struct_0('#skF_2'), C_62)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_62)), '#skF_2') | ~r2_hidden(C_62, '#skF_3') | ~m1_subset_1(C_62, u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), C_62), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_111])).
% 2.22/1.35  tff(c_119, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_7)), '#skF_2') | ~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.22/1.35  tff(c_123, plain, (![B_63]: (k6_domain_1(u1_struct_0('#skF_2'), B_63)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_63)), '#skF_2') | ~r2_hidden(B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_33, c_119])).
% 2.22/1.35  tff(c_127, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_7, '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_53, c_123])).
% 2.22/1.35  tff(c_130, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_127])).
% 2.22/1.35  tff(c_131, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_33, c_130])).
% 2.22/1.35  tff(c_134, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(reflexivity, [status(thm), theory('equality')], [c_131])).
% 2.22/1.35  tff(c_136, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_134])).
% 2.22/1.35  tff(c_140, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_136])).
% 2.22/1.35  tff(c_143, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_140])).
% 2.22/1.35  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_143])).
% 2.22/1.35  tff(c_146, plain, (![A_31]: (~r2_hidden(A_31, '#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.22/1.35  tff(c_172, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77, B_78), B_78) | v2_tex_2(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v3_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.22/1.35  tff(c_179, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_172])).
% 2.22/1.35  tff(c_184, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_179])).
% 2.22/1.35  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_146, c_184])).
% 2.22/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  Inference rules
% 2.22/1.35  ----------------------
% 2.22/1.35  #Ref     : 1
% 2.22/1.35  #Sup     : 28
% 2.22/1.35  #Fact    : 0
% 2.22/1.35  #Define  : 0
% 2.22/1.36  #Split   : 1
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 5
% 2.22/1.36  #Demod        : 25
% 2.22/1.36  #Tautology    : 5
% 2.22/1.36  #SimpNegUnit  : 7
% 2.22/1.36  #BackRed      : 0
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.36  Preprocessing        : 0.31
% 2.22/1.36  Parsing              : 0.18
% 2.22/1.36  CNF conversion       : 0.02
% 2.22/1.36  Main loop            : 0.21
% 2.22/1.36  Inferencing          : 0.09
% 2.22/1.36  Reduction            : 0.05
% 2.22/1.36  Demodulation         : 0.04
% 2.22/1.36  BG Simplification    : 0.01
% 2.22/1.36  Subsumption          : 0.03
% 2.22/1.36  Abstraction          : 0.01
% 2.22/1.36  MUC search           : 0.00
% 2.22/1.36  Cooper               : 0.00
% 2.22/1.36  Total                : 0.55
% 2.22/1.36  Index Insertion      : 0.00
% 2.22/1.36  Index Deletion       : 0.00
% 2.22/1.36  Index Matching       : 0.00
% 2.22/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
