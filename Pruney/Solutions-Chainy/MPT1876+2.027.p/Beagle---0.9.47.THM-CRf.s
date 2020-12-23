%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:54 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 211 expanded)
%              Number of leaves         :   37 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  262 ( 771 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_100,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v1_tdlat_3(B) )
           => ( ~ v2_struct_0(B)
              & v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc31_tex_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_24,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'(A_19),A_19)
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_95,plain,(
    ! [A_45,C_46,B_47] :
      ( m1_subset_1(A_45,C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_102,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_86,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_144,plain,(
    ! [A_52] :
      ( k6_domain_1(A_52,'#skF_1'(A_52)) = k1_tarski('#skF_1'(A_52))
      | ~ v1_zfmisc_1(A_52)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_22,plain,(
    ! [A_19] :
      ( k6_domain_1(A_19,'#skF_1'(A_19)) = A_19
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_189,plain,(
    ! [A_57] :
      ( k1_tarski('#skF_1'(A_57)) = A_57
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_22])).

tff(c_63,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_69,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_66])).

tff(c_103,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k6_domain_1(A_14,B_15) = k1_tarski(B_15)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [A_48] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_48) = k1_tarski(A_48)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_103,c_14])).

tff(c_109,plain,(
    ! [A_48] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_48) = k1_tarski(A_48)
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_106])).

tff(c_172,plain,(
    ! [A_53,B_54] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_53),B_54),A_53)
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_179,plain,(
    ! [A_48] :
      ( v2_tex_2(k1_tarski(A_48),'#skF_3')
      | ~ m1_subset_1(A_48,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_172])).

tff(c_185,plain,(
    ! [A_48] :
      ( v2_tex_2(k1_tarski(A_48),'#skF_3')
      | ~ m1_subset_1(A_48,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_179])).

tff(c_186,plain,(
    ! [A_48] :
      ( v2_tex_2(k1_tarski(A_48),'#skF_3')
      | ~ m1_subset_1(A_48,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_185])).

tff(c_281,plain,(
    ! [A_70] :
      ( v2_tex_2(A_70,'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_70),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_70),'#skF_4')
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70)
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_186])).

tff(c_292,plain,(
    ! [A_71] :
      ( v2_tex_2(A_71,'#skF_3')
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | ~ r2_hidden('#skF_1'(A_71),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_281])).

tff(c_295,plain,(
    ! [A_71] :
      ( v2_tex_2(A_71,'#skF_3')
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1('#skF_1'(A_71),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_292])).

tff(c_299,plain,(
    ! [A_72] :
      ( v2_tex_2(A_72,'#skF_3')
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72)
      | ~ m1_subset_1('#skF_1'(A_72),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_295])).

tff(c_303,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_299])).

tff(c_306,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_303])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_60,c_306])).

tff(c_309,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_650,plain,(
    ! [A_119,B_120] :
      ( m1_pre_topc('#skF_2'(A_119,B_120),A_119)
      | ~ v2_tex_2(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | v1_xboole_0(B_120)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_658,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_650])).

tff(c_663,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_309,c_658])).

tff(c_664,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_663])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( l1_pre_topc(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_702,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_664,c_10])).

tff(c_709,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_702])).

tff(c_8,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_538,plain,(
    ! [A_111,B_112] :
      ( ~ v2_struct_0('#skF_2'(A_111,B_112))
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | v1_xboole_0(B_112)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_545,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_538])).

tff(c_549,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_309,c_545])).

tff(c_550,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_549])).

tff(c_44,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_525,plain,(
    ! [A_109,B_110] :
      ( v1_tdlat_3('#skF_2'(A_109,B_110))
      | ~ v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_532,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_525])).

tff(c_536,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_309,c_532])).

tff(c_537,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_536])).

tff(c_16,plain,(
    ! [B_18,A_16] :
      ( v7_struct_0(B_18)
      | ~ v1_tdlat_3(B_18)
      | v2_struct_0(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_tdlat_3(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_699,plain,
    ( v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_664,c_16])).

tff(c_705,plain,
    ( v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_537,c_699])).

tff(c_706,plain,(
    v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_550,c_705])).

tff(c_310,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_632,plain,(
    ! [A_117,B_118] :
      ( u1_struct_0('#skF_2'(A_117,B_118)) = B_118
      | ~ v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | v1_xboole_0(B_118)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_643,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_632])).

tff(c_648,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_309,c_643])).

tff(c_649,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_648])).

tff(c_12,plain,(
    ! [A_13] :
      ( v1_zfmisc_1(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | ~ v7_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_685,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_12])).

tff(c_695,plain,
    ( ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_310,c_685])).

tff(c_711,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_695])).

tff(c_715,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_711])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n004.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 18:44:53 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.40  
% 2.92/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.40  %$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.92/1.40  
% 2.92/1.40  %Foreground sorts:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Background operators:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Foreground operators:
% 2.92/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.40  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.92/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.40  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.92/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.92/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.92/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.92/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.92/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.92/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.92/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.92/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.40  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.92/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.40  
% 2.92/1.42  tff(f_161, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 2.92/1.42  tff(f_100, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.92/1.42  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.92/1.42  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.92/1.42  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.92/1.42  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.92/1.42  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.92/1.42  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 2.92/1.42  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.92/1.42  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.92/1.42  tff(f_90, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & v1_tdlat_3(B)) => (~v2_struct_0(B) & v7_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc31_tex_2)).
% 2.92/1.42  tff(f_61, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.92/1.42  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_40, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_56, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_58, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 2.92/1.42  tff(c_50, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_60, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 2.92/1.42  tff(c_24, plain, (![A_19]: (m1_subset_1('#skF_1'(A_19), A_19) | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.92/1.42  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.92/1.42  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_95, plain, (![A_45, C_46, B_47]: (m1_subset_1(A_45, C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.42  tff(c_102, plain, (![A_45]: (m1_subset_1(A_45, u1_struct_0('#skF_3')) | ~r2_hidden(A_45, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_95])).
% 2.92/1.42  tff(c_86, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.92/1.42  tff(c_144, plain, (![A_52]: (k6_domain_1(A_52, '#skF_1'(A_52))=k1_tarski('#skF_1'(A_52)) | ~v1_zfmisc_1(A_52) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_24, c_86])).
% 2.92/1.42  tff(c_22, plain, (![A_19]: (k6_domain_1(A_19, '#skF_1'(A_19))=A_19 | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.92/1.42  tff(c_189, plain, (![A_57]: (k1_tarski('#skF_1'(A_57))=A_57 | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_144, c_22])).
% 2.92/1.42  tff(c_63, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.42  tff(c_66, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_63])).
% 2.92/1.42  tff(c_69, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_66])).
% 2.92/1.42  tff(c_103, plain, (![A_48]: (m1_subset_1(A_48, u1_struct_0('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_95])).
% 2.92/1.42  tff(c_14, plain, (![A_14, B_15]: (k6_domain_1(A_14, B_15)=k1_tarski(B_15) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.92/1.42  tff(c_106, plain, (![A_48]: (k6_domain_1(u1_struct_0('#skF_3'), A_48)=k1_tarski(A_48) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_103, c_14])).
% 2.92/1.42  tff(c_109, plain, (![A_48]: (k6_domain_1(u1_struct_0('#skF_3'), A_48)=k1_tarski(A_48) | ~r2_hidden(A_48, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_69, c_106])).
% 2.92/1.42  tff(c_172, plain, (![A_53, B_54]: (v2_tex_2(k6_domain_1(u1_struct_0(A_53), B_54), A_53) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.92/1.42  tff(c_179, plain, (![A_48]: (v2_tex_2(k1_tarski(A_48), '#skF_3') | ~m1_subset_1(A_48, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_48, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_172])).
% 2.92/1.42  tff(c_185, plain, (![A_48]: (v2_tex_2(k1_tarski(A_48), '#skF_3') | ~m1_subset_1(A_48, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(A_48, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_179])).
% 2.92/1.42  tff(c_186, plain, (![A_48]: (v2_tex_2(k1_tarski(A_48), '#skF_3') | ~m1_subset_1(A_48, u1_struct_0('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_185])).
% 2.92/1.42  tff(c_281, plain, (![A_70]: (v2_tex_2(A_70, '#skF_3') | ~m1_subset_1('#skF_1'(A_70), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(A_70), '#skF_4') | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_189, c_186])).
% 2.92/1.42  tff(c_292, plain, (![A_71]: (v2_tex_2(A_71, '#skF_3') | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | ~r2_hidden('#skF_1'(A_71), '#skF_4'))), inference(resolution, [status(thm)], [c_102, c_281])).
% 2.92/1.42  tff(c_295, plain, (![A_71]: (v2_tex_2(A_71, '#skF_3') | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_1'(A_71), '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_292])).
% 2.92/1.42  tff(c_299, plain, (![A_72]: (v2_tex_2(A_72, '#skF_3') | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72) | ~m1_subset_1('#skF_1'(A_72), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_295])).
% 2.92/1.42  tff(c_303, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_299])).
% 2.92/1.42  tff(c_306, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_303])).
% 2.92/1.42  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_60, c_306])).
% 2.92/1.42  tff(c_309, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 2.92/1.42  tff(c_650, plain, (![A_119, B_120]: (m1_pre_topc('#skF_2'(A_119, B_120), A_119) | ~v2_tex_2(B_120, A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | v1_xboole_0(B_120) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.92/1.42  tff(c_658, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_650])).
% 2.92/1.42  tff(c_663, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_309, c_658])).
% 2.92/1.42  tff(c_664, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_663])).
% 2.92/1.42  tff(c_10, plain, (![B_12, A_10]: (l1_pre_topc(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.42  tff(c_702, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_664, c_10])).
% 2.92/1.42  tff(c_709, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_702])).
% 2.92/1.42  tff(c_8, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.42  tff(c_538, plain, (![A_111, B_112]: (~v2_struct_0('#skF_2'(A_111, B_112)) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | v1_xboole_0(B_112) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.92/1.42  tff(c_545, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_538])).
% 2.92/1.42  tff(c_549, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_309, c_545])).
% 2.92/1.42  tff(c_550, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_549])).
% 2.92/1.42  tff(c_44, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.92/1.42  tff(c_525, plain, (![A_109, B_110]: (v1_tdlat_3('#skF_2'(A_109, B_110)) | ~v2_tex_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.92/1.42  tff(c_532, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_525])).
% 2.92/1.42  tff(c_536, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_309, c_532])).
% 2.92/1.42  tff(c_537, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_536])).
% 2.92/1.42  tff(c_16, plain, (![B_18, A_16]: (v7_struct_0(B_18) | ~v1_tdlat_3(B_18) | v2_struct_0(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16) | ~v2_tdlat_3(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.92/1.42  tff(c_699, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_664, c_16])).
% 2.92/1.42  tff(c_705, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_537, c_699])).
% 2.92/1.42  tff(c_706, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_550, c_705])).
% 2.92/1.42  tff(c_310, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.92/1.42  tff(c_632, plain, (![A_117, B_118]: (u1_struct_0('#skF_2'(A_117, B_118))=B_118 | ~v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | v1_xboole_0(B_118) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.92/1.42  tff(c_643, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_632])).
% 2.92/1.42  tff(c_648, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_309, c_643])).
% 2.92/1.42  tff(c_649, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_648])).
% 2.92/1.42  tff(c_12, plain, (![A_13]: (v1_zfmisc_1(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | ~v7_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.42  tff(c_685, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_649, c_12])).
% 2.92/1.42  tff(c_695, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_310, c_685])).
% 2.92/1.42  tff(c_711, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_695])).
% 2.92/1.42  tff(c_715, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_711])).
% 2.92/1.42  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_709, c_715])).
% 2.92/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.42  
% 2.92/1.42  Inference rules
% 2.92/1.42  ----------------------
% 2.92/1.42  #Ref     : 0
% 2.92/1.42  #Sup     : 120
% 2.92/1.42  #Fact    : 0
% 2.92/1.42  #Define  : 0
% 2.92/1.42  #Split   : 10
% 2.92/1.42  #Chain   : 0
% 2.92/1.42  #Close   : 0
% 2.92/1.42  
% 2.92/1.42  Ordering : KBO
% 2.92/1.42  
% 2.92/1.42  Simplification rules
% 2.92/1.42  ----------------------
% 2.92/1.42  #Subsume      : 18
% 2.92/1.42  #Demod        : 39
% 2.92/1.42  #Tautology    : 30
% 2.92/1.42  #SimpNegUnit  : 47
% 2.92/1.42  #BackRed      : 0
% 2.92/1.42  
% 2.92/1.42  #Partial instantiations: 0
% 2.92/1.42  #Strategies tried      : 1
% 2.92/1.42  
% 2.92/1.42  Timing (in seconds)
% 2.92/1.42  ----------------------
% 2.92/1.42  Preprocessing        : 0.33
% 2.92/1.42  Parsing              : 0.18
% 2.92/1.42  CNF conversion       : 0.02
% 2.92/1.42  Main loop            : 0.35
% 2.92/1.42  Inferencing          : 0.13
% 2.92/1.42  Reduction            : 0.10
% 2.92/1.42  Demodulation         : 0.06
% 2.92/1.42  BG Simplification    : 0.02
% 2.92/1.42  Subsumption          : 0.07
% 2.92/1.42  Abstraction          : 0.02
% 2.92/1.42  MUC search           : 0.00
% 2.92/1.42  Cooper               : 0.00
% 2.92/1.42  Total                : 0.71
% 2.92/1.42  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
