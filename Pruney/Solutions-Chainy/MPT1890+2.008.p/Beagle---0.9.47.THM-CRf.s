%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 171 expanded)
%              Number of leaves         :   34 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 ( 597 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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

tff(f_102,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    ! [A_22,B_30] :
      ( m1_subset_1('#skF_4'(A_22,B_30),u1_struct_0(A_22))
      | v2_tex_2(B_30,A_22)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_439,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_4'(A_114,B_115),B_115)
      | v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_451,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_439])).

tff(c_458,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_451])).

tff(c_459,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36,c_458])).

tff(c_55,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59),B_60)
      | ~ r1_tarski(A_59,B_60)
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | ~ r1_tarski(A_62,B_61)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_114,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_59,c_102])).

tff(c_115,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_44,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k6_domain_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_219,plain,(
    ! [A_88,B_89] :
      ( v4_pre_topc(k2_pre_topc(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_234,plain,(
    ! [A_88,B_15] :
      ( v4_pre_topc(k2_pre_topc(A_88,k6_domain_1(u1_struct_0(A_88),B_15)),A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ m1_subset_1(B_15,u1_struct_0(A_88))
      | v1_xboole_0(u1_struct_0(A_88)) ) ),
    inference(resolution,[status(thm)],[c_18,c_219])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_pre_topc(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_315,plain,(
    ! [B_103,A_104] :
      ( v3_pre_topc(B_103,A_104)
      | ~ v4_pre_topc(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v3_tdlat_3(A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1232,plain,(
    ! [A_203,B_204] :
      ( v3_pre_topc(k2_pre_topc(A_203,B_204),A_203)
      | ~ v4_pre_topc(k2_pre_topc(A_203,B_204),A_203)
      | ~ v3_tdlat_3(A_203)
      | ~ v2_pre_topc(A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(resolution,[status(thm)],[c_16,c_315])).

tff(c_2595,plain,(
    ! [A_386,B_387] :
      ( v3_pre_topc(k2_pre_topc(A_386,k6_domain_1(u1_struct_0(A_386),B_387)),A_386)
      | ~ v3_tdlat_3(A_386)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_386),B_387),k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | ~ m1_subset_1(B_387,u1_struct_0(A_386))
      | v1_xboole_0(u1_struct_0(A_386)) ) ),
    inference(resolution,[status(thm)],[c_234,c_1232])).

tff(c_2604,plain,(
    ! [A_388,B_389] :
      ( v3_pre_topc(k2_pre_topc(A_388,k6_domain_1(u1_struct_0(A_388),B_389)),A_388)
      | ~ v3_tdlat_3(A_388)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | ~ m1_subset_1(B_389,u1_struct_0(A_388))
      | v1_xboole_0(u1_struct_0(A_388)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2595])).

tff(c_38,plain,(
    ! [C_40] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_40))) = k6_domain_1(u1_struct_0('#skF_5'),C_40)
      | ~ r2_hidden(C_40,'#skF_6')
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_707,plain,(
    ! [A_144,B_145,D_146] :
      ( k9_subset_1(u1_struct_0(A_144),B_145,D_146) != k6_domain_1(u1_struct_0(A_144),'#skF_4'(A_144,B_145))
      | ~ v3_pre_topc(D_146,A_144)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_709,plain,(
    ! [C_40] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_40) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_40)),'#skF_5')
      | ~ m1_subset_1(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_40)),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_40,'#skF_6')
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_707])).

tff(c_711,plain,(
    ! [C_40] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_40) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_40)),'#skF_5')
      | ~ m1_subset_1(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_40)),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_tex_2('#skF_6','#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_40,'#skF_6')
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_709])).

tff(c_798,plain,(
    ! [C_152] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_152) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_152)),'#skF_5')
      | ~ m1_subset_1(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_152)),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_152,'#skF_6')
      | ~ m1_subset_1(C_152,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36,c_711])).

tff(c_801,plain,(
    ! [C_152] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_152) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_152)),'#skF_5')
      | ~ r2_hidden(C_152,'#skF_6')
      | ~ m1_subset_1(C_152,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),C_152),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_798])).

tff(c_1165,plain,(
    ! [C_193] :
      ( k6_domain_1(u1_struct_0('#skF_5'),C_193) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),C_193)),'#skF_5')
      | ~ r2_hidden(C_193,'#skF_6')
      | ~ m1_subset_1(C_193,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),C_193),k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_801])).

tff(c_1169,plain,(
    ! [B_15] :
      ( k6_domain_1(u1_struct_0('#skF_5'),B_15) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_15)),'#skF_5')
      | ~ r2_hidden(B_15,'#skF_6')
      | ~ m1_subset_1(B_15,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_18,c_1165])).

tff(c_1175,plain,(
    ! [B_15] :
      ( k6_domain_1(u1_struct_0('#skF_5'),B_15) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_15)),'#skF_5')
      | ~ r2_hidden(B_15,'#skF_6')
      | ~ m1_subset_1(B_15,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1169])).

tff(c_2608,plain,(
    ! [B_389] :
      ( k6_domain_1(u1_struct_0('#skF_5'),B_389) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ r2_hidden(B_389,'#skF_6')
      | ~ v3_tdlat_3('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2604,c_1175])).

tff(c_2611,plain,(
    ! [B_389] :
      ( k6_domain_1(u1_struct_0('#skF_5'),B_389) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ r2_hidden(B_389,'#skF_6')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_44,c_2608])).

tff(c_2612,plain,(
    ! [B_389] :
      ( k6_domain_1(u1_struct_0('#skF_5'),B_389) != k6_domain_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6'))
      | ~ r2_hidden(B_389,'#skF_6')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_2611])).

tff(c_2615,plain,
    ( ~ r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2612])).

tff(c_2617,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_2615])).

tff(c_2621,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_2617])).

tff(c_2624,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_2621])).

tff(c_2626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36,c_2624])).

tff(c_2627,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_2824,plain,(
    ! [A_424,B_425] :
      ( r2_hidden('#skF_4'(A_424,B_425),B_425)
      | v2_tex_2(B_425,A_424)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2836,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2824])).

tff(c_2843,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2836])).

tff(c_2844,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36,c_2843])).

tff(c_2849,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2844,c_2])).

tff(c_2856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.17  
% 5.78/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.17  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.78/2.17  
% 5.78/2.17  %Foreground sorts:
% 5.78/2.17  
% 5.78/2.17  
% 5.78/2.17  %Background operators:
% 5.78/2.17  
% 5.78/2.17  
% 5.78/2.17  %Foreground operators:
% 5.78/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.78/2.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.78/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.78/2.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.78/2.17  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.78/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.78/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.78/2.17  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.78/2.17  tff('#skF_6', type, '#skF_6': $i).
% 5.78/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.78/2.17  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.78/2.17  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.78/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.17  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.78/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.78/2.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.78/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.78/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.17  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.78/2.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.78/2.17  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.78/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.17  
% 6.21/2.19  tff(f_124, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 6.21/2.19  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 6.21/2.19  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.21/2.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.21/2.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.21/2.19  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.21/2.19  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 6.21/2.19  tff(f_48, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.21/2.19  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 6.21/2.19  tff(c_48, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_36, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_46, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_42, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_34, plain, (![A_22, B_30]: (m1_subset_1('#skF_4'(A_22, B_30), u1_struct_0(A_22)) | v2_tex_2(B_30, A_22) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.21/2.19  tff(c_439, plain, (![A_114, B_115]: (r2_hidden('#skF_4'(A_114, B_115), B_115) | v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.21/2.19  tff(c_451, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_439])).
% 6.21/2.19  tff(c_458, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_451])).
% 6.21/2.19  tff(c_459, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_36, c_458])).
% 6.21/2.19  tff(c_55, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.21/2.19  tff(c_59, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_55])).
% 6.21/2.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.19  tff(c_86, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.21/2.19  tff(c_94, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59), B_60) | ~r1_tarski(A_59, B_60) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_4, c_86])).
% 6.21/2.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.19  tff(c_102, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | ~r1_tarski(A_62, B_61) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_94, c_2])).
% 6.21/2.19  tff(c_114, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_59, c_102])).
% 6.21/2.19  tff(c_115, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_114])).
% 6.21/2.19  tff(c_44, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k6_domain_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.21/2.19  tff(c_219, plain, (![A_88, B_89]: (v4_pre_topc(k2_pre_topc(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.21/2.19  tff(c_234, plain, (![A_88, B_15]: (v4_pre_topc(k2_pre_topc(A_88, k6_domain_1(u1_struct_0(A_88), B_15)), A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~m1_subset_1(B_15, u1_struct_0(A_88)) | v1_xboole_0(u1_struct_0(A_88)))), inference(resolution, [status(thm)], [c_18, c_219])).
% 6.21/2.19  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k2_pre_topc(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.21/2.19  tff(c_315, plain, (![B_103, A_104]: (v3_pre_topc(B_103, A_104) | ~v4_pre_topc(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~v3_tdlat_3(A_104) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.21/2.19  tff(c_1232, plain, (![A_203, B_204]: (v3_pre_topc(k2_pre_topc(A_203, B_204), A_203) | ~v4_pre_topc(k2_pre_topc(A_203, B_204), A_203) | ~v3_tdlat_3(A_203) | ~v2_pre_topc(A_203) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(resolution, [status(thm)], [c_16, c_315])).
% 6.21/2.19  tff(c_2595, plain, (![A_386, B_387]: (v3_pre_topc(k2_pre_topc(A_386, k6_domain_1(u1_struct_0(A_386), B_387)), A_386) | ~v3_tdlat_3(A_386) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_386), B_387), k1_zfmisc_1(u1_struct_0(A_386))) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | ~m1_subset_1(B_387, u1_struct_0(A_386)) | v1_xboole_0(u1_struct_0(A_386)))), inference(resolution, [status(thm)], [c_234, c_1232])).
% 6.21/2.19  tff(c_2604, plain, (![A_388, B_389]: (v3_pre_topc(k2_pre_topc(A_388, k6_domain_1(u1_struct_0(A_388), B_389)), A_388) | ~v3_tdlat_3(A_388) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | ~m1_subset_1(B_389, u1_struct_0(A_388)) | v1_xboole_0(u1_struct_0(A_388)))), inference(resolution, [status(thm)], [c_18, c_2595])).
% 6.21/2.19  tff(c_38, plain, (![C_40]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_40)))=k6_domain_1(u1_struct_0('#skF_5'), C_40) | ~r2_hidden(C_40, '#skF_6') | ~m1_subset_1(C_40, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.21/2.19  tff(c_707, plain, (![A_144, B_145, D_146]: (k9_subset_1(u1_struct_0(A_144), B_145, D_146)!=k6_domain_1(u1_struct_0(A_144), '#skF_4'(A_144, B_145)) | ~v3_pre_topc(D_146, A_144) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_144))) | v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.21/2.19  tff(c_709, plain, (![C_40]: (k6_domain_1(u1_struct_0('#skF_5'), C_40)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_40)), '#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_40)), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_40, '#skF_6') | ~m1_subset_1(C_40, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_707])).
% 6.21/2.19  tff(c_711, plain, (![C_40]: (k6_domain_1(u1_struct_0('#skF_5'), C_40)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_40)), '#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_40)), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_40, '#skF_6') | ~m1_subset_1(C_40, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_709])).
% 6.21/2.19  tff(c_798, plain, (![C_152]: (k6_domain_1(u1_struct_0('#skF_5'), C_152)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_152)), '#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_152)), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_152, '#skF_6') | ~m1_subset_1(C_152, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_48, c_36, c_711])).
% 6.21/2.19  tff(c_801, plain, (![C_152]: (k6_domain_1(u1_struct_0('#skF_5'), C_152)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_152)), '#skF_5') | ~r2_hidden(C_152, '#skF_6') | ~m1_subset_1(C_152, u1_struct_0('#skF_5')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), C_152), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_798])).
% 6.21/2.19  tff(c_1165, plain, (![C_193]: (k6_domain_1(u1_struct_0('#skF_5'), C_193)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), C_193)), '#skF_5') | ~r2_hidden(C_193, '#skF_6') | ~m1_subset_1(C_193, u1_struct_0('#skF_5')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), C_193), k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_801])).
% 6.21/2.19  tff(c_1169, plain, (![B_15]: (k6_domain_1(u1_struct_0('#skF_5'), B_15)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_15)), '#skF_5') | ~r2_hidden(B_15, '#skF_6') | ~m1_subset_1(B_15, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_18, c_1165])).
% 6.21/2.19  tff(c_1175, plain, (![B_15]: (k6_domain_1(u1_struct_0('#skF_5'), B_15)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_15)), '#skF_5') | ~r2_hidden(B_15, '#skF_6') | ~m1_subset_1(B_15, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_115, c_1169])).
% 6.21/2.19  tff(c_2608, plain, (![B_389]: (k6_domain_1(u1_struct_0('#skF_5'), B_389)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~r2_hidden(B_389, '#skF_6') | ~v3_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_389, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2604, c_1175])).
% 6.21/2.19  tff(c_2611, plain, (![B_389]: (k6_domain_1(u1_struct_0('#skF_5'), B_389)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~r2_hidden(B_389, '#skF_6') | ~m1_subset_1(B_389, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_44, c_2608])).
% 6.21/2.19  tff(c_2612, plain, (![B_389]: (k6_domain_1(u1_struct_0('#skF_5'), B_389)!=k6_domain_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')) | ~r2_hidden(B_389, '#skF_6') | ~m1_subset_1(B_389, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_115, c_2611])).
% 6.21/2.19  tff(c_2615, plain, (~r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(reflexivity, [status(thm), theory('equality')], [c_2612])).
% 6.21/2.19  tff(c_2617, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_459, c_2615])).
% 6.21/2.19  tff(c_2621, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_2617])).
% 6.21/2.19  tff(c_2624, plain, (v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_2621])).
% 6.21/2.19  tff(c_2626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_36, c_2624])).
% 6.21/2.19  tff(c_2627, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_114])).
% 6.21/2.19  tff(c_2824, plain, (![A_424, B_425]: (r2_hidden('#skF_4'(A_424, B_425), B_425) | v2_tex_2(B_425, A_424) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_424))) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.21/2.19  tff(c_2836, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_2824])).
% 6.21/2.19  tff(c_2843, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2836])).
% 6.21/2.19  tff(c_2844, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_36, c_2843])).
% 6.21/2.19  tff(c_2849, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2844, c_2])).
% 6.21/2.19  tff(c_2856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2849])).
% 6.21/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.19  
% 6.21/2.19  Inference rules
% 6.21/2.19  ----------------------
% 6.21/2.19  #Ref     : 1
% 6.21/2.19  #Sup     : 668
% 6.21/2.19  #Fact    : 0
% 6.21/2.19  #Define  : 0
% 6.21/2.19  #Split   : 13
% 6.21/2.19  #Chain   : 0
% 6.21/2.19  #Close   : 0
% 6.21/2.19  
% 6.21/2.19  Ordering : KBO
% 6.21/2.19  
% 6.21/2.19  Simplification rules
% 6.21/2.19  ----------------------
% 6.21/2.19  #Subsume      : 291
% 6.21/2.19  #Demod        : 130
% 6.21/2.19  #Tautology    : 62
% 6.21/2.19  #SimpNegUnit  : 21
% 6.21/2.19  #BackRed      : 8
% 6.21/2.19  
% 6.21/2.19  #Partial instantiations: 0
% 6.21/2.19  #Strategies tried      : 1
% 6.21/2.19  
% 6.21/2.19  Timing (in seconds)
% 6.21/2.19  ----------------------
% 6.21/2.19  Preprocessing        : 0.32
% 6.21/2.19  Parsing              : 0.18
% 6.21/2.19  CNF conversion       : 0.02
% 6.21/2.19  Main loop            : 1.10
% 6.21/2.19  Inferencing          : 0.39
% 6.21/2.19  Reduction            : 0.27
% 6.21/2.19  Demodulation         : 0.16
% 6.21/2.19  BG Simplification    : 0.03
% 6.21/2.19  Subsumption          : 0.33
% 6.21/2.19  Abstraction          : 0.04
% 6.21/2.19  MUC search           : 0.00
% 6.21/2.19  Cooper               : 0.00
% 6.21/2.19  Total                : 1.45
% 6.21/2.19  Index Insertion      : 0.00
% 6.21/2.19  Index Deletion       : 0.00
% 6.21/2.19  Index Matching       : 0.00
% 6.21/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
