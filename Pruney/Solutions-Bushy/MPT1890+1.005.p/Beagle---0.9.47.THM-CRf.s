%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1890+1.005 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:39 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 136 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 ( 538 expanded)
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

tff(f_113,negated_conjecture,(
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

tff(f_86,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_13,B_21] :
      ( m1_subset_1('#skF_1'(A_13,B_21),u1_struct_0(A_13))
      | v2_tex_2(B_21,A_13)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v3_tdlat_3(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_55)
      | v2_tex_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_107,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_112,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_107])).

tff(c_113,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_112])).

tff(c_34,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_39,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k6_domain_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [A_50,B_51] :
      ( v4_pre_topc(k2_pre_topc(A_50,B_51),A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_50,B_7] :
      ( v4_pre_topc(k2_pre_topc(A_50,k6_domain_1(u1_struct_0(A_50),B_7)),A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | ~ m1_subset_1(B_7,u1_struct_0(A_50))
      | v1_xboole_0(u1_struct_0(A_50)) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [C_33] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_33))) = k6_domain_1(u1_struct_0('#skF_2'),C_33)
      | ~ r2_hidden(C_33,'#skF_3')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_144,plain,(
    ! [A_71,B_72,D_73] :
      ( k9_subset_1(u1_struct_0(A_71),B_72,D_73) != k6_domain_1(u1_struct_0(A_71),'#skF_1'(A_71,B_72))
      | ~ v4_pre_topc(D_73,A_71)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(u1_struct_0(A_71)))
      | v2_tex_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_146,plain,(
    ! [C_33] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_33) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_33)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_33)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_33,'#skF_3')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_144])).

tff(c_148,plain,(
    ! [C_33] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_33) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_33)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_33)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_33,'#skF_3')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_146])).

tff(c_179,plain,(
    ! [C_88] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_88) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_88)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_88)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_88,'#skF_3')
      | ~ m1_subset_1(C_88,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_148])).

tff(c_182,plain,(
    ! [C_88] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_88) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_88)),'#skF_2')
      | ~ r2_hidden(C_88,'#skF_3')
      | ~ m1_subset_1(C_88,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_88),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4,c_179])).

tff(c_186,plain,(
    ! [C_89] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_89) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_89)),'#skF_2')
      | ~ r2_hidden(C_89,'#skF_3')
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_89),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_182])).

tff(c_190,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_7)),'#skF_2')
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6,c_186])).

tff(c_194,plain,(
    ! [B_90] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_90) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_90)),'#skF_2')
      | ~ r2_hidden(B_90,'#skF_3')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_190])).

tff(c_198,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_80,c_194])).

tff(c_201,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_198])).

tff(c_202,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_201])).

tff(c_205,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_202])).

tff(c_207,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_205])).

tff(c_211,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_207])).

tff(c_217,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_211])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_217])).

tff(c_220,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_282,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_1'(A_108,B_109),B_109)
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v3_tdlat_3(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_289,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_282])).

tff(c_294,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_289])).

tff(c_295,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_294])).

tff(c_18,plain,(
    ! [B_28,A_27] :
      ( ~ v1_xboole_0(B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_298,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_295,c_18])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_298])).

%------------------------------------------------------------------------------
