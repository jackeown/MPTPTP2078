%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 301 expanded)
%              Number of leaves         :   30 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  209 ( 941 expanded)
%              Number of equality atoms :   19 ( 139 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_10,c_38])).

tff(c_47,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_28])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_202,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1('#skF_1'(A_72,B_73),u1_struct_0(A_72))
      | v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v3_tdlat_3(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_205,plain,(
    ! [B_73] :
      ( m1_subset_1('#skF_1'('#skF_2',B_73),k2_struct_0('#skF_2'))
      | v2_tex_2(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_202])).

tff(c_207,plain,(
    ! [B_73] :
      ( m1_subset_1('#skF_1'('#skF_2',B_73),k2_struct_0('#skF_2'))
      | v2_tex_2(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_47,c_205])).

tff(c_208,plain,(
    ! [B_73] :
      ( m1_subset_1('#skF_1'('#skF_2',B_73),k2_struct_0('#skF_2'))
      | v2_tex_2(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_207])).

tff(c_142,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),B_64)
      | v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v3_tdlat_3(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_152,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'('#skF_2',B_64),B_64)
      | v2_tex_2(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_142])).

tff(c_157,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'('#skF_2',B_64),B_64)
      | v2_tex_2(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_152])).

tff(c_160,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'('#skF_2',B_66),B_66)
      | v2_tex_2(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_157])).

tff(c_170,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_160])).

tff(c_176,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_170])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k6_domain_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    ! [A_60,B_61] :
      ( v4_pre_topc(k2_pre_topc(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_117,plain,(
    ! [B_61] :
      ( v4_pre_topc(k2_pre_topc('#skF_2',B_61),'#skF_2')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_107])).

tff(c_123,plain,(
    ! [B_62] :
      ( v4_pre_topc(k2_pre_topc('#skF_2',B_62),'#skF_2')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_117])).

tff(c_139,plain,(
    ! [B_13] :
      ( v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),B_13)),'#skF_2')
      | ~ m1_subset_1(B_13,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_186,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_12,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k2_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_186,c_12])).

tff(c_192,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_189])).

tff(c_195,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_195])).

tff(c_200,plain,(
    ! [B_13] :
      ( v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),B_13)),'#skF_2')
      | ~ m1_subset_1(B_13,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_201,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_94,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k2_pre_topc(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    ! [B_58] :
      ( m1_subset_1(k2_pre_topc('#skF_2',B_58),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_94])).

tff(c_102,plain,(
    ! [B_58] :
      ( m1_subset_1(k2_pre_topc('#skF_2',B_58),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_47,c_99])).

tff(c_26,plain,(
    ! [C_34] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_34))) = k6_domain_1(u1_struct_0('#skF_2'),C_34)
      | ~ r2_hidden(C_34,'#skF_3')
      | ~ m1_subset_1(C_34,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_57,plain,(
    ! [C_34] :
      ( k9_subset_1(k2_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_34))) = k6_domain_1(k2_struct_0('#skF_2'),C_34)
      | ~ r2_hidden(C_34,'#skF_3')
      | ~ m1_subset_1(C_34,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_47,c_47,c_47,c_26])).

tff(c_233,plain,(
    ! [A_86,B_87,D_88] :
      ( k9_subset_1(u1_struct_0(A_86),B_87,D_88) != k6_domain_1(u1_struct_0(A_86),'#skF_1'(A_86,B_87))
      | ~ v4_pre_topc(D_88,A_86)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(u1_struct_0(A_86)))
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v3_tdlat_3(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_235,plain,(
    ! [B_87,D_88] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_87,D_88) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2',B_87))
      | ~ v4_pre_topc(D_88,'#skF_2')
      | ~ m1_subset_1(D_88,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2(B_87,'#skF_2')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_233])).

tff(c_239,plain,(
    ! [B_87,D_88] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_87,D_88) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2',B_87))
      | ~ v4_pre_topc(D_88,'#skF_2')
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_tex_2(B_87,'#skF_2')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_47,c_47,c_47,c_235])).

tff(c_257,plain,(
    ! [B_93,D_94] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_93,D_94) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2',B_93))
      | ~ v4_pre_topc(D_94,'#skF_2')
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_tex_2(B_93,'#skF_2')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_239])).

tff(c_259,plain,(
    ! [C_34] :
      ( k6_domain_1(k2_struct_0('#skF_2'),C_34) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_34)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_34)),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ r2_hidden(C_34,'#skF_3')
      | ~ m1_subset_1(C_34,k2_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_257])).

tff(c_261,plain,(
    ! [C_34] :
      ( k6_domain_1(k2_struct_0('#skF_2'),C_34) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_34)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_34)),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ r2_hidden(C_34,'#skF_3')
      | ~ m1_subset_1(C_34,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_259])).

tff(c_330,plain,(
    ! [C_109] :
      ( k6_domain_1(k2_struct_0('#skF_2'),C_109) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_109)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_109)),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ r2_hidden(C_109,'#skF_3')
      | ~ m1_subset_1(C_109,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_261])).

tff(c_365,plain,(
    ! [C_116] :
      ( k6_domain_1(k2_struct_0('#skF_2'),C_116) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),C_116)),'#skF_2')
      | ~ r2_hidden(C_116,'#skF_3')
      | ~ m1_subset_1(C_116,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(k2_struct_0('#skF_2'),C_116),k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_102,c_330])).

tff(c_369,plain,(
    ! [B_13] :
      ( k6_domain_1(k2_struct_0('#skF_2'),B_13) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),B_13)),'#skF_2')
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_365])).

tff(c_373,plain,(
    ! [B_117] :
      ( k6_domain_1(k2_struct_0('#skF_2'),B_117) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),B_117)),'#skF_2')
      | ~ r2_hidden(B_117,'#skF_3')
      | ~ m1_subset_1(B_117,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_369])).

tff(c_377,plain,(
    ! [B_13] :
      ( k6_domain_1(k2_struct_0('#skF_2'),B_13) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_200,c_373])).

tff(c_380,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k2_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_377])).

tff(c_382,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_380])).

tff(c_394,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_208,c_382])).

tff(c_400,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_394])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.50  
% 3.06/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.51  %$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.51  
% 3.06/1.51  %Foreground sorts:
% 3.06/1.51  
% 3.06/1.51  
% 3.06/1.51  %Background operators:
% 3.06/1.51  
% 3.06/1.51  
% 3.06/1.51  %Foreground operators:
% 3.06/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.06/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.06/1.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.06/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.06/1.51  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.06/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.06/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.06/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.06/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.06/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.06/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.51  
% 3.20/1.52  tff(f_122, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 3.20/1.52  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.52  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.52  tff(f_100, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tex_2)).
% 3.20/1.52  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.20/1.52  tff(f_72, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.20/1.52  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.20/1.52  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.20/1.52  tff(c_24, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_10, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.52  tff(c_38, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.52  tff(c_43, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_10, c_38])).
% 3.20/1.52  tff(c_47, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_43])).
% 3.20/1.52  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_28])).
% 3.20/1.52  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_32, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_202, plain, (![A_72, B_73]: (m1_subset_1('#skF_1'(A_72, B_73), u1_struct_0(A_72)) | v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v3_tdlat_3(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.20/1.52  tff(c_205, plain, (![B_73]: (m1_subset_1('#skF_1'('#skF_2', B_73), k2_struct_0('#skF_2')) | v2_tex_2(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_202])).
% 3.20/1.52  tff(c_207, plain, (![B_73]: (m1_subset_1('#skF_1'('#skF_2', B_73), k2_struct_0('#skF_2')) | v2_tex_2(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_47, c_205])).
% 3.20/1.52  tff(c_208, plain, (![B_73]: (m1_subset_1('#skF_1'('#skF_2', B_73), k2_struct_0('#skF_2')) | v2_tex_2(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_207])).
% 3.20/1.52  tff(c_142, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), B_64) | v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v3_tdlat_3(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.20/1.52  tff(c_152, plain, (![B_64]: (r2_hidden('#skF_1'('#skF_2', B_64), B_64) | v2_tex_2(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_142])).
% 3.20/1.52  tff(c_157, plain, (![B_64]: (r2_hidden('#skF_1'('#skF_2', B_64), B_64) | v2_tex_2(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_152])).
% 3.20/1.52  tff(c_160, plain, (![B_66]: (r2_hidden('#skF_1'('#skF_2', B_66), B_66) | v2_tex_2(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_157])).
% 3.20/1.52  tff(c_170, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_160])).
% 3.20/1.52  tff(c_176, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24, c_170])).
% 3.20/1.52  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k6_domain_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.52  tff(c_107, plain, (![A_60, B_61]: (v4_pre_topc(k2_pre_topc(A_60, B_61), A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.52  tff(c_117, plain, (![B_61]: (v4_pre_topc(k2_pre_topc('#skF_2', B_61), '#skF_2') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_107])).
% 3.20/1.52  tff(c_123, plain, (![B_62]: (v4_pre_topc(k2_pre_topc('#skF_2', B_62), '#skF_2') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_117])).
% 3.20/1.52  tff(c_139, plain, (![B_13]: (v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), B_13)), '#skF_2') | ~m1_subset_1(B_13, k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_123])).
% 3.20/1.52  tff(c_186, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_139])).
% 3.20/1.52  tff(c_12, plain, (![A_11]: (~v1_xboole_0(k2_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.52  tff(c_189, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_186, c_12])).
% 3.20/1.52  tff(c_192, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_189])).
% 3.20/1.52  tff(c_195, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_192])).
% 3.20/1.52  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_195])).
% 3.20/1.52  tff(c_200, plain, (![B_13]: (v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), B_13)), '#skF_2') | ~m1_subset_1(B_13, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_139])).
% 3.20/1.52  tff(c_201, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_139])).
% 3.20/1.52  tff(c_94, plain, (![A_57, B_58]: (m1_subset_1(k2_pre_topc(A_57, B_58), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.52  tff(c_99, plain, (![B_58]: (m1_subset_1(k2_pre_topc('#skF_2', B_58), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_94])).
% 3.20/1.52  tff(c_102, plain, (![B_58]: (m1_subset_1(k2_pre_topc('#skF_2', B_58), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_47, c_99])).
% 3.20/1.52  tff(c_26, plain, (![C_34]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_34)))=k6_domain_1(u1_struct_0('#skF_2'), C_34) | ~r2_hidden(C_34, '#skF_3') | ~m1_subset_1(C_34, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_57, plain, (![C_34]: (k9_subset_1(k2_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_34)))=k6_domain_1(k2_struct_0('#skF_2'), C_34) | ~r2_hidden(C_34, '#skF_3') | ~m1_subset_1(C_34, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_47, c_47, c_47, c_26])).
% 3.20/1.52  tff(c_233, plain, (![A_86, B_87, D_88]: (k9_subset_1(u1_struct_0(A_86), B_87, D_88)!=k6_domain_1(u1_struct_0(A_86), '#skF_1'(A_86, B_87)) | ~v4_pre_topc(D_88, A_86) | ~m1_subset_1(D_88, k1_zfmisc_1(u1_struct_0(A_86))) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v3_tdlat_3(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.20/1.52  tff(c_235, plain, (![B_87, D_88]: (k9_subset_1(k2_struct_0('#skF_2'), B_87, D_88)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', B_87)) | ~v4_pre_topc(D_88, '#skF_2') | ~m1_subset_1(D_88, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2(B_87, '#skF_2') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_233])).
% 3.20/1.52  tff(c_239, plain, (![B_87, D_88]: (k9_subset_1(k2_struct_0('#skF_2'), B_87, D_88)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', B_87)) | ~v4_pre_topc(D_88, '#skF_2') | ~m1_subset_1(D_88, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_tex_2(B_87, '#skF_2') | ~m1_subset_1(B_87, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_47, c_47, c_47, c_235])).
% 3.20/1.52  tff(c_257, plain, (![B_93, D_94]: (k9_subset_1(k2_struct_0('#skF_2'), B_93, D_94)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', B_93)) | ~v4_pre_topc(D_94, '#skF_2') | ~m1_subset_1(D_94, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_tex_2(B_93, '#skF_2') | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_239])).
% 3.20/1.52  tff(c_259, plain, (![C_34]: (k6_domain_1(k2_struct_0('#skF_2'), C_34)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_34)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_34)), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~r2_hidden(C_34, '#skF_3') | ~m1_subset_1(C_34, k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57, c_257])).
% 3.20/1.52  tff(c_261, plain, (![C_34]: (k6_domain_1(k2_struct_0('#skF_2'), C_34)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_34)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_34)), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | ~r2_hidden(C_34, '#skF_3') | ~m1_subset_1(C_34, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_259])).
% 3.20/1.52  tff(c_330, plain, (![C_109]: (k6_domain_1(k2_struct_0('#skF_2'), C_109)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_109)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_109)), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~r2_hidden(C_109, '#skF_3') | ~m1_subset_1(C_109, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_261])).
% 3.20/1.52  tff(c_365, plain, (![C_116]: (k6_domain_1(k2_struct_0('#skF_2'), C_116)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), C_116)), '#skF_2') | ~r2_hidden(C_116, '#skF_3') | ~m1_subset_1(C_116, k2_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(k2_struct_0('#skF_2'), C_116), k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_102, c_330])).
% 3.20/1.52  tff(c_369, plain, (![B_13]: (k6_domain_1(k2_struct_0('#skF_2'), B_13)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), B_13)), '#skF_2') | ~r2_hidden(B_13, '#skF_3') | ~m1_subset_1(B_13, k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_365])).
% 3.20/1.52  tff(c_373, plain, (![B_117]: (k6_domain_1(k2_struct_0('#skF_2'), B_117)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), B_117)), '#skF_2') | ~r2_hidden(B_117, '#skF_3') | ~m1_subset_1(B_117, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_201, c_369])).
% 3.20/1.52  tff(c_377, plain, (![B_13]: (k6_domain_1(k2_struct_0('#skF_2'), B_13)!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_13, '#skF_3') | ~m1_subset_1(B_13, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_200, c_373])).
% 3.20/1.52  tff(c_380, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k2_struct_0('#skF_2'))), inference(reflexivity, [status(thm), theory('equality')], [c_377])).
% 3.20/1.52  tff(c_382, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_380])).
% 3.20/1.52  tff(c_394, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_208, c_382])).
% 3.20/1.52  tff(c_400, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_394])).
% 3.20/1.52  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_400])).
% 3.20/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  Inference rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Ref     : 1
% 3.20/1.52  #Sup     : 70
% 3.20/1.52  #Fact    : 0
% 3.20/1.52  #Define  : 0
% 3.20/1.52  #Split   : 1
% 3.20/1.52  #Chain   : 0
% 3.20/1.52  #Close   : 0
% 3.20/1.52  
% 3.20/1.52  Ordering : KBO
% 3.20/1.52  
% 3.20/1.52  Simplification rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Subsume      : 19
% 3.20/1.52  #Demod        : 102
% 3.20/1.52  #Tautology    : 7
% 3.20/1.52  #SimpNegUnit  : 22
% 3.20/1.52  #BackRed      : 2
% 3.20/1.52  
% 3.20/1.52  #Partial instantiations: 0
% 3.20/1.52  #Strategies tried      : 1
% 3.20/1.52  
% 3.20/1.52  Timing (in seconds)
% 3.20/1.52  ----------------------
% 3.20/1.53  Preprocessing        : 0.35
% 3.20/1.53  Parsing              : 0.19
% 3.20/1.53  CNF conversion       : 0.03
% 3.20/1.53  Main loop            : 0.35
% 3.20/1.53  Inferencing          : 0.14
% 3.20/1.53  Reduction            : 0.10
% 3.20/1.53  Demodulation         : 0.07
% 3.20/1.53  BG Simplification    : 0.02
% 3.20/1.53  Subsumption          : 0.06
% 3.20/1.53  Abstraction          : 0.02
% 3.20/1.53  MUC search           : 0.00
% 3.20/1.53  Cooper               : 0.00
% 3.20/1.53  Total                : 0.74
% 3.20/1.53  Index Insertion      : 0.00
% 3.20/1.53  Index Deletion       : 0.00
% 3.20/1.53  Index Matching       : 0.00
% 3.20/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
