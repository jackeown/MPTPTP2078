%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:23 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 137 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  210 ( 529 expanded)
%              Number of equality atoms :   14 (  43 expanded)
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

tff(f_134,negated_conjecture,(
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

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_26,plain,(
    ! [A_20,B_28] :
      ( m1_subset_1('#skF_2'(A_20,B_28),u1_struct_0(A_20))
      | v2_tex_2(B_28,A_20)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_190,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79),B_79)
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_199,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_205,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_199])).

tff(c_206,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_28,c_205])).

tff(c_41,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_46,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_36,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k6_domain_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    ! [A_55,B_56] :
      ( v4_pre_topc(k2_pre_topc(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    ! [A_55,B_10] :
      ( v4_pre_topc(k2_pre_topc(A_55,k6_domain_1(u1_struct_0(A_55),B_10)),A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | ~ m1_subset_1(B_10,u1_struct_0(A_55))
      | v1_xboole_0(u1_struct_0(A_55)) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    ! [B_71,A_72] :
      ( v3_pre_topc(B_71,A_72)
      | ~ v4_pre_topc(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ v3_tdlat_3(A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_241,plain,(
    ! [A_94,B_95] :
      ( v3_pre_topc(k2_pre_topc(A_94,B_95),A_94)
      | ~ v4_pre_topc(k2_pre_topc(A_94,B_95),A_94)
      | ~ v3_tdlat_3(A_94)
      | ~ v2_pre_topc(A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_292,plain,(
    ! [A_119,B_120] :
      ( v3_pre_topc(k2_pre_topc(A_119,k6_domain_1(u1_struct_0(A_119),B_120)),A_119)
      | ~ v3_tdlat_3(A_119)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_119),B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | v1_xboole_0(u1_struct_0(A_119)) ) ),
    inference(resolution,[status(thm)],[c_90,c_241])).

tff(c_297,plain,(
    ! [A_121,B_122] :
      ( v3_pre_topc(k2_pre_topc(A_121,k6_domain_1(u1_struct_0(A_121),B_122)),A_121)
      | ~ v3_tdlat_3(A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | v1_xboole_0(u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_8,c_292])).

tff(c_30,plain,(
    ! [C_38] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_38))) = k6_domain_1(u1_struct_0('#skF_3'),C_38)
      | ~ r2_hidden(C_38,'#skF_4')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_234,plain,(
    ! [A_90,B_91,D_92] :
      ( k9_subset_1(u1_struct_0(A_90),B_91,D_92) != k6_domain_1(u1_struct_0(A_90),'#skF_2'(A_90,B_91))
      | ~ v3_pre_topc(D_92,A_90)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(u1_struct_0(A_90)))
      | v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_236,plain,(
    ! [C_38] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_38) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_38)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_38)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_38,'#skF_4')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_234])).

tff(c_238,plain,(
    ! [C_38] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_38) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_38)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_38)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_38,'#skF_4')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_32,c_236])).

tff(c_256,plain,(
    ! [C_96] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_96) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_96)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_96)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_96,'#skF_4')
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_28,c_238])).

tff(c_259,plain,(
    ! [C_96] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_96) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_96)),'#skF_3')
      | ~ r2_hidden(C_96,'#skF_4')
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_96),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_282,plain,(
    ! [C_115] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_115) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_115)),'#skF_3')
      | ~ r2_hidden(C_115,'#skF_4')
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_115),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_259])).

tff(c_286,plain,(
    ! [B_10] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_10) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_10)),'#skF_3')
      | ~ r2_hidden(B_10,'#skF_4')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_282])).

tff(c_289,plain,(
    ! [B_10] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_10) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_10)),'#skF_3')
      | ~ r2_hidden(B_10,'#skF_4')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_286])).

tff(c_301,plain,(
    ! [B_122] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_122) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_122,'#skF_4')
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_297,c_289])).

tff(c_304,plain,(
    ! [B_122] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_122) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_122,'#skF_4')
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_36,c_301])).

tff(c_305,plain,(
    ! [B_122] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_122) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_122,'#skF_4')
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_304])).

tff(c_308,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_305])).

tff(c_310,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_308])).

tff(c_314,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_310])).

tff(c_320,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_32,c_314])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_28,c_320])).

tff(c_323,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_412,plain,(
    ! [B_148,A_149] :
      ( v2_tex_2(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ v1_xboole_0(B_148)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_425,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_412])).

tff(c_431,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_323,c_425])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_28,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:01:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.78/1.42  
% 2.78/1.42  %Foreground sorts:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Background operators:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Foreground operators:
% 2.78/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.78/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.78/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.78/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.42  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.78/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.78/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.42  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.78/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.78/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.42  
% 2.78/1.43  tff(f_134, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 2.78/1.43  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 2.78/1.43  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.78/1.43  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.78/1.43  tff(f_59, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.78/1.43  tff(f_44, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.78/1.43  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.78/1.43  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.78/1.43  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_28, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_26, plain, (![A_20, B_28]: (m1_subset_1('#skF_2'(A_20, B_28), u1_struct_0(A_20)) | v2_tex_2(B_28, A_20) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.78/1.43  tff(c_190, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79), B_79) | v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.78/1.43  tff(c_199, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_190])).
% 2.78/1.43  tff(c_205, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_199])).
% 2.78/1.43  tff(c_206, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_28, c_205])).
% 2.78/1.43  tff(c_41, plain, (![B_39, A_40]: (v1_xboole_0(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.43  tff(c_45, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.78/1.43  tff(c_46, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_45])).
% 2.78/1.43  tff(c_36, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_8, plain, (![A_9, B_10]: (m1_subset_1(k6_domain_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.43  tff(c_81, plain, (![A_55, B_56]: (v4_pre_topc(k2_pre_topc(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.43  tff(c_90, plain, (![A_55, B_10]: (v4_pre_topc(k2_pre_topc(A_55, k6_domain_1(u1_struct_0(A_55), B_10)), A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | ~m1_subset_1(B_10, u1_struct_0(A_55)) | v1_xboole_0(u1_struct_0(A_55)))), inference(resolution, [status(thm)], [c_8, c_81])).
% 2.78/1.43  tff(c_6, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.78/1.43  tff(c_151, plain, (![B_71, A_72]: (v3_pre_topc(B_71, A_72) | ~v4_pre_topc(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~v3_tdlat_3(A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.43  tff(c_241, plain, (![A_94, B_95]: (v3_pre_topc(k2_pre_topc(A_94, B_95), A_94) | ~v4_pre_topc(k2_pre_topc(A_94, B_95), A_94) | ~v3_tdlat_3(A_94) | ~v2_pre_topc(A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_6, c_151])).
% 2.78/1.43  tff(c_292, plain, (![A_119, B_120]: (v3_pre_topc(k2_pre_topc(A_119, k6_domain_1(u1_struct_0(A_119), B_120)), A_119) | ~v3_tdlat_3(A_119) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_119), B_120), k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | v1_xboole_0(u1_struct_0(A_119)))), inference(resolution, [status(thm)], [c_90, c_241])).
% 2.78/1.43  tff(c_297, plain, (![A_121, B_122]: (v3_pre_topc(k2_pre_topc(A_121, k6_domain_1(u1_struct_0(A_121), B_122)), A_121) | ~v3_tdlat_3(A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | v1_xboole_0(u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_8, c_292])).
% 2.78/1.43  tff(c_30, plain, (![C_38]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_38)))=k6_domain_1(u1_struct_0('#skF_3'), C_38) | ~r2_hidden(C_38, '#skF_4') | ~m1_subset_1(C_38, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.78/1.43  tff(c_234, plain, (![A_90, B_91, D_92]: (k9_subset_1(u1_struct_0(A_90), B_91, D_92)!=k6_domain_1(u1_struct_0(A_90), '#skF_2'(A_90, B_91)) | ~v3_pre_topc(D_92, A_90) | ~m1_subset_1(D_92, k1_zfmisc_1(u1_struct_0(A_90))) | v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.78/1.43  tff(c_236, plain, (![C_38]: (k6_domain_1(u1_struct_0('#skF_3'), C_38)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_38)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_38)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_38, '#skF_4') | ~m1_subset_1(C_38, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_234])).
% 2.78/1.43  tff(c_238, plain, (![C_38]: (k6_domain_1(u1_struct_0('#skF_3'), C_38)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_38)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_38)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_38, '#skF_4') | ~m1_subset_1(C_38, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_32, c_236])).
% 2.78/1.43  tff(c_256, plain, (![C_96]: (k6_domain_1(u1_struct_0('#skF_3'), C_96)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_96)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_96)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_96, '#skF_4') | ~m1_subset_1(C_96, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_28, c_238])).
% 2.78/1.43  tff(c_259, plain, (![C_96]: (k6_domain_1(u1_struct_0('#skF_3'), C_96)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_96)), '#skF_3') | ~r2_hidden(C_96, '#skF_4') | ~m1_subset_1(C_96, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_96), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_256])).
% 2.78/1.43  tff(c_282, plain, (![C_115]: (k6_domain_1(u1_struct_0('#skF_3'), C_115)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_115)), '#skF_3') | ~r2_hidden(C_115, '#skF_4') | ~m1_subset_1(C_115, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_115), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_259])).
% 2.78/1.43  tff(c_286, plain, (![B_10]: (k6_domain_1(u1_struct_0('#skF_3'), B_10)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_10)), '#skF_3') | ~r2_hidden(B_10, '#skF_4') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_282])).
% 2.78/1.43  tff(c_289, plain, (![B_10]: (k6_domain_1(u1_struct_0('#skF_3'), B_10)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_10)), '#skF_3') | ~r2_hidden(B_10, '#skF_4') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_286])).
% 2.78/1.43  tff(c_301, plain, (![B_122]: (k6_domain_1(u1_struct_0('#skF_3'), B_122)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_122, '#skF_4') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_122, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_297, c_289])).
% 2.78/1.43  tff(c_304, plain, (![B_122]: (k6_domain_1(u1_struct_0('#skF_3'), B_122)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_122, '#skF_4') | ~m1_subset_1(B_122, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_36, c_301])).
% 2.78/1.43  tff(c_305, plain, (![B_122]: (k6_domain_1(u1_struct_0('#skF_3'), B_122)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_122, '#skF_4') | ~m1_subset_1(B_122, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_304])).
% 2.78/1.43  tff(c_308, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_305])).
% 2.78/1.43  tff(c_310, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_308])).
% 2.78/1.43  tff(c_314, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_310])).
% 2.78/1.43  tff(c_320, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_32, c_314])).
% 2.78/1.43  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_28, c_320])).
% 2.78/1.43  tff(c_323, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_45])).
% 2.78/1.43  tff(c_412, plain, (![B_148, A_149]: (v2_tex_2(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~v1_xboole_0(B_148) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.78/1.43  tff(c_425, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_412])).
% 2.78/1.43  tff(c_431, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_323, c_425])).
% 2.78/1.43  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_28, c_431])).
% 2.78/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  Inference rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Ref     : 1
% 2.78/1.43  #Sup     : 75
% 2.78/1.43  #Fact    : 0
% 2.78/1.43  #Define  : 0
% 2.78/1.43  #Split   : 3
% 2.78/1.43  #Chain   : 0
% 2.78/1.44  #Close   : 0
% 2.78/1.44  
% 2.78/1.44  Ordering : KBO
% 2.78/1.44  
% 2.78/1.44  Simplification rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Subsume      : 7
% 2.78/1.44  #Demod        : 38
% 2.78/1.44  #Tautology    : 12
% 2.78/1.44  #SimpNegUnit  : 8
% 2.78/1.44  #BackRed      : 0
% 2.78/1.44  
% 2.78/1.44  #Partial instantiations: 0
% 2.78/1.44  #Strategies tried      : 1
% 2.78/1.44  
% 2.78/1.44  Timing (in seconds)
% 2.78/1.44  ----------------------
% 2.78/1.44  Preprocessing        : 0.31
% 2.78/1.44  Parsing              : 0.17
% 2.78/1.44  CNF conversion       : 0.02
% 2.78/1.44  Main loop            : 0.35
% 2.78/1.44  Inferencing          : 0.16
% 2.78/1.44  Reduction            : 0.08
% 2.78/1.44  Demodulation         : 0.06
% 2.78/1.44  BG Simplification    : 0.02
% 2.78/1.44  Subsumption          : 0.06
% 2.78/1.44  Abstraction          : 0.01
% 2.78/1.44  MUC search           : 0.00
% 2.78/1.44  Cooper               : 0.00
% 2.78/1.44  Total                : 0.70
% 2.78/1.44  Index Insertion      : 0.00
% 2.78/1.44  Index Deletion       : 0.00
% 2.78/1.44  Index Matching       : 0.00
% 2.78/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
