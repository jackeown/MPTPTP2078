%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:38 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 183 expanded)
%              Number of leaves         :   24 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 932 expanded)
%              Number of equality atoms :    8 (  77 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
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

tff(f_63,axiom,(
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

tff(f_37,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_5,B_13] :
      ( m1_subset_1('#skF_2'(A_5,B_13),u1_struct_0(A_5))
      | v2_tex_2(B_13,A_5)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),B_53)
      | v2_tex_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_100,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_92])).

tff(c_101,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18,c_100])).

tff(c_34,plain,(
    ! [C_32] :
      ( m1_subset_1('#skF_5'(C_32),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [C_32] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'(C_32)) = k6_domain_1(u1_struct_0('#skF_3'),C_32)
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_115,plain,(
    ! [A_60,B_61,D_62] :
      ( k9_subset_1(u1_struct_0(A_60),B_61,D_62) != k6_domain_1(u1_struct_0(A_60),'#skF_2'(A_60,B_61))
      | ~ v3_pre_topc(D_62,A_60)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(u1_struct_0(A_60)))
      | v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_117,plain,(
    ! [C_32] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_32) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_32),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_115])).

tff(c_119,plain,(
    ! [C_32] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_32) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_32),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_20,c_117])).

tff(c_121,plain,(
    ! [C_63] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_63) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_63),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_63),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_63,'#skF_4')
      | ~ m1_subset_1(C_63,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18,c_119])).

tff(c_125,plain,(
    ! [C_32] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_32) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_128,plain,
    ( ~ v3_pre_topc('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125])).

tff(c_130,plain,
    ( ~ v3_pre_topc('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_128])).

tff(c_132,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_135,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_132])).

tff(c_141,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_20,c_135])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_18,c_141])).

tff(c_145,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_32,plain,(
    ! [C_32] :
      ( v4_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_53,plain,(
    ! [B_47,A_48] :
      ( v3_pre_topc(B_47,A_48)
      | ~ v4_pre_topc(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v3_tdlat_3(A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [C_32] :
      ( v3_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ v4_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_71,plain,(
    ! [C_49] :
      ( v3_pre_topc('#skF_5'(C_49),'#skF_3')
      | ~ v4_pre_topc('#skF_5'(C_49),'#skF_3')
      | ~ r2_hidden(C_49,'#skF_4')
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_24,c_56])).

tff(c_75,plain,(
    ! [C_32] :
      ( v3_pre_topc('#skF_5'(C_32),'#skF_3')
      | ~ r2_hidden(C_32,'#skF_4')
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_144,plain,(
    ~ v3_pre_topc('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_148,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_144])).

tff(c_151,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_148])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_151])).

%------------------------------------------------------------------------------
