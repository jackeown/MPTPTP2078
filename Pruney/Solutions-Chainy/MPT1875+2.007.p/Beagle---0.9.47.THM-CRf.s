%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 155 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 405 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

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

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_140,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_107,plain,(
    ! [A_61,B_62] :
      ( m1_pre_topc(k1_pre_topc(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_117,plain,(
    m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_113])).

tff(c_71,plain,(
    ! [A_56,B_57] :
      ( u1_struct_0(k1_pre_topc(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_77,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_4')) = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_81,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_77])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | ~ v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_4')
    | ~ l1_struct_0(k1_pre_topc('#skF_3','#skF_4'))
    | ~ v2_struct_0(k1_pre_topc('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_14])).

tff(c_105,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_138,plain,(
    ! [B_65,A_66] :
      ( v1_tdlat_3(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v1_tdlat_3(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_144,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_138])).

tff(c_148,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_144])).

tff(c_149,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_148])).

tff(c_18,plain,(
    ! [B_17,A_15] :
      ( m1_subset_1(u1_struct_0(B_17),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_pre_topc(B_17,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_541,plain,(
    ! [B_111,A_112] :
      ( v2_tex_2(u1_struct_0(B_111),A_112)
      | ~ v1_tdlat_3(B_111)
      | ~ m1_subset_1(u1_struct_0(B_111),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_pre_topc(B_111,A_112)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_575,plain,(
    ! [B_113,A_114] :
      ( v2_tex_2(u1_struct_0(B_113),A_114)
      | ~ v1_tdlat_3(B_113)
      | v2_struct_0(B_113)
      | v2_struct_0(A_114)
      | ~ m1_pre_topc(B_113,A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_18,c_541])).

tff(c_584,plain,(
    ! [A_114] :
      ( v2_tex_2('#skF_4',A_114)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0(k1_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0(A_114)
      | ~ m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_575])).

tff(c_586,plain,(
    ! [A_114] :
      ( v2_tex_2('#skF_4',A_114)
      | v2_struct_0(k1_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0(A_114)
      | ~ m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_584])).

tff(c_588,plain,(
    ! [A_115] :
      ( v2_tex_2('#skF_4',A_115)
      | v2_struct_0(A_115)
      | ~ m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_586])).

tff(c_591,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_588])).

tff(c_594,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_591])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_594])).

tff(c_597,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_600,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_604,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_600])).

tff(c_605,plain,(
    ! [A_117,B_118] :
      ( m1_pre_topc(k1_pre_topc(A_117,B_118),A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_611,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_605])).

tff(c_615,plain,(
    m1_pre_topc(k1_pre_topc('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_611])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( l1_pre_topc(B_10)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_621,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_615,c_12])).

tff(c_627,plain,(
    l1_pre_topc(k1_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_621])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_627])).

tff(c_630,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_901,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_2'(A_149,B_150),B_150)
      | v2_tex_2(B_150,A_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_913,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_901])).

tff(c_920,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_913])).

tff(c_921,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_920])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_924,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_921,c_2])).

tff(c_928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/2.06  
% 3.85/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/2.06  %$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.85/2.06  
% 3.85/2.06  %Foreground sorts:
% 3.85/2.06  
% 3.85/2.06  
% 3.85/2.06  %Background operators:
% 3.85/2.06  
% 3.85/2.06  
% 3.85/2.06  %Foreground operators:
% 3.85/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/2.06  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.85/2.06  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.85/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/2.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.85/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/2.06  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.85/2.06  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.85/2.06  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.85/2.06  tff('#skF_3', type, '#skF_3': $i).
% 3.85/2.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.85/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.85/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/2.06  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.85/2.06  tff('#skF_4', type, '#skF_4': $i).
% 3.85/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.85/2.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.85/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/2.06  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.85/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/2.06  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.85/2.06  
% 3.85/2.08  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.85/2.08  tff(f_155, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.85/2.08  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 3.85/2.08  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 3.85/2.08  tff(f_56, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 3.85/2.08  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 3.85/2.08  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.85/2.08  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 3.85/2.08  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.85/2.08  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 3.85/2.08  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.85/2.08  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/2.08  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/2.08  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/2.08  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/2.08  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/2.08  tff(c_107, plain, (![A_61, B_62]: (m1_pre_topc(k1_pre_topc(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/2.08  tff(c_113, plain, (m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_107])).
% 3.85/2.08  tff(c_117, plain, (m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_113])).
% 3.85/2.08  tff(c_71, plain, (![A_56, B_57]: (u1_struct_0(k1_pre_topc(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.85/2.08  tff(c_77, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_71])).
% 3.85/2.08  tff(c_81, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_77])).
% 3.85/2.08  tff(c_14, plain, (![A_11]: (v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | ~v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.85/2.08  tff(c_97, plain, (v1_xboole_0('#skF_4') | ~l1_struct_0(k1_pre_topc('#skF_3', '#skF_4')) | ~v2_struct_0(k1_pre_topc('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_14])).
% 3.85/2.08  tff(c_105, plain, (~v2_struct_0(k1_pre_topc('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_97])).
% 3.85/2.08  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/2.08  tff(c_44, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/2.08  tff(c_138, plain, (![B_65, A_66]: (v1_tdlat_3(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66) | ~v1_tdlat_3(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.85/2.08  tff(c_144, plain, (v1_tdlat_3(k1_pre_topc('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_117, c_138])).
% 3.85/2.08  tff(c_148, plain, (v1_tdlat_3(k1_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_144])).
% 3.85/2.08  tff(c_149, plain, (v1_tdlat_3(k1_pre_topc('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_148])).
% 3.85/2.08  tff(c_18, plain, (![B_17, A_15]: (m1_subset_1(u1_struct_0(B_17), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_pre_topc(B_17, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.85/2.08  tff(c_541, plain, (![B_111, A_112]: (v2_tex_2(u1_struct_0(B_111), A_112) | ~v1_tdlat_3(B_111) | ~m1_subset_1(u1_struct_0(B_111), k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_pre_topc(B_111, A_112) | v2_struct_0(B_111) | ~l1_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.85/2.08  tff(c_575, plain, (![B_113, A_114]: (v2_tex_2(u1_struct_0(B_113), A_114) | ~v1_tdlat_3(B_113) | v2_struct_0(B_113) | v2_struct_0(A_114) | ~m1_pre_topc(B_113, A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_18, c_541])).
% 3.85/2.08  tff(c_584, plain, (![A_114]: (v2_tex_2('#skF_4', A_114) | ~v1_tdlat_3(k1_pre_topc('#skF_3', '#skF_4')) | v2_struct_0(k1_pre_topc('#skF_3', '#skF_4')) | v2_struct_0(A_114) | ~m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), A_114) | ~l1_pre_topc(A_114))), inference(superposition, [status(thm), theory('equality')], [c_81, c_575])).
% 3.85/2.08  tff(c_586, plain, (![A_114]: (v2_tex_2('#skF_4', A_114) | v2_struct_0(k1_pre_topc('#skF_3', '#skF_4')) | v2_struct_0(A_114) | ~m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_584])).
% 3.85/2.08  tff(c_588, plain, (![A_115]: (v2_tex_2('#skF_4', A_115) | v2_struct_0(A_115) | ~m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), A_115) | ~l1_pre_topc(A_115))), inference(negUnitSimplification, [status(thm)], [c_105, c_586])).
% 3.85/2.08  tff(c_591, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_117, c_588])).
% 3.85/2.08  tff(c_594, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_591])).
% 3.85/2.08  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_594])).
% 3.85/2.08  tff(c_597, plain, (~l1_struct_0(k1_pre_topc('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_97])).
% 3.85/2.08  tff(c_600, plain, (~l1_struct_0(k1_pre_topc('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_597])).
% 3.85/2.08  tff(c_604, plain, (~l1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_600])).
% 3.85/2.08  tff(c_605, plain, (![A_117, B_118]: (m1_pre_topc(k1_pre_topc(A_117, B_118), A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/2.08  tff(c_611, plain, (m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_605])).
% 3.85/2.08  tff(c_615, plain, (m1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_611])).
% 3.85/2.08  tff(c_12, plain, (![B_10, A_8]: (l1_pre_topc(B_10) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/2.08  tff(c_621, plain, (l1_pre_topc(k1_pre_topc('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_615, c_12])).
% 3.85/2.08  tff(c_627, plain, (l1_pre_topc(k1_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_621])).
% 3.85/2.08  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_604, c_627])).
% 3.85/2.08  tff(c_630, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_597])).
% 3.85/2.08  tff(c_901, plain, (![A_149, B_150]: (r2_hidden('#skF_2'(A_149, B_150), B_150) | v2_tex_2(B_150, A_149) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.85/2.08  tff(c_913, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_901])).
% 3.85/2.08  tff(c_920, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_913])).
% 3.85/2.08  tff(c_921, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_920])).
% 3.85/2.08  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/2.08  tff(c_924, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_921, c_2])).
% 3.85/2.08  tff(c_928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_630, c_924])).
% 3.85/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/2.08  
% 3.85/2.08  Inference rules
% 3.85/2.08  ----------------------
% 3.85/2.08  #Ref     : 0
% 3.85/2.08  #Sup     : 193
% 3.85/2.08  #Fact    : 0
% 3.85/2.08  #Define  : 0
% 3.85/2.08  #Split   : 5
% 3.85/2.08  #Chain   : 0
% 3.85/2.08  #Close   : 0
% 3.85/2.08  
% 3.85/2.08  Ordering : KBO
% 3.85/2.08  
% 3.85/2.08  Simplification rules
% 3.85/2.08  ----------------------
% 3.85/2.08  #Subsume      : 25
% 3.85/2.08  #Demod        : 106
% 3.85/2.08  #Tautology    : 33
% 3.85/2.08  #SimpNegUnit  : 16
% 3.85/2.08  #BackRed      : 0
% 3.85/2.08  
% 3.85/2.08  #Partial instantiations: 0
% 3.85/2.08  #Strategies tried      : 1
% 3.85/2.08  
% 3.85/2.08  Timing (in seconds)
% 3.85/2.08  ----------------------
% 3.85/2.08  Preprocessing        : 0.51
% 3.85/2.08  Parsing              : 0.28
% 3.85/2.08  CNF conversion       : 0.04
% 3.85/2.08  Main loop            : 0.61
% 3.85/2.08  Inferencing          : 0.23
% 3.85/2.08  Reduction            : 0.17
% 3.85/2.08  Demodulation         : 0.12
% 3.85/2.08  BG Simplification    : 0.04
% 3.85/2.08  Subsumption          : 0.13
% 3.85/2.08  Abstraction          : 0.02
% 3.85/2.08  MUC search           : 0.00
% 3.85/2.08  Cooper               : 0.00
% 3.85/2.08  Total                : 1.16
% 3.85/2.08  Index Insertion      : 0.00
% 3.85/2.08  Index Deletion       : 0.00
% 3.85/2.08  Index Matching       : 0.00
% 3.85/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
