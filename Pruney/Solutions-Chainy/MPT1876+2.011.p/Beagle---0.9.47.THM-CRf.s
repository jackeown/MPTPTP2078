%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 480 expanded)
%              Number of leaves         :   43 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          :  307 (1598 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_209,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_148,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_189,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_177,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_83,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_74,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_85,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_74])).

tff(c_8,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_251,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(A_89,B_88)
      | ~ v1_zfmisc_1(B_88)
      | v1_xboole_0(B_88)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_260,plain,(
    ! [A_9,B_10] :
      ( k1_tarski(A_9) = B_10
      | ~ v1_zfmisc_1(B_10)
      | v1_xboole_0(B_10)
      | v1_xboole_0(k1_tarski(A_9))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_251])).

tff(c_292,plain,(
    ! [A_91,B_92] :
      ( k1_tarski(A_91) = B_92
      | ~ v1_zfmisc_1(B_92)
      | v1_xboole_0(B_92)
      | ~ r2_hidden(A_91,B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_260])).

tff(c_305,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_292])).

tff(c_164,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_242,plain,(
    ! [A_85,B_86,A_87] :
      ( r1_tarski(A_85,B_86)
      | ~ r1_tarski(A_85,k1_tarski(A_87))
      | ~ r2_hidden(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_164])).

tff(c_346,plain,(
    ! [A_98,B_99,A_100] :
      ( r1_tarski(k1_tarski(A_98),B_99)
      | ~ r2_hidden(A_100,B_99)
      | ~ r2_hidden(A_98,k1_tarski(A_100)) ) ),
    inference(resolution,[status(thm)],[c_12,c_242])).

tff(c_530,plain,(
    ! [A_117,A_118] :
      ( r1_tarski(k1_tarski(A_117),A_118)
      | ~ r2_hidden(A_117,k1_tarski('#skF_1'(A_118)))
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_4,c_346])).

tff(c_549,plain,(
    ! [A_118] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_118)))),A_118)
      | v1_xboole_0(A_118)
      | v1_xboole_0(k1_tarski('#skF_1'(A_118))) ) ),
    inference(resolution,[status(thm)],[c_4,c_530])).

tff(c_557,plain,(
    ! [A_118] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_118)))),A_118)
      | v1_xboole_0(A_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_549])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_102,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_102])).

tff(c_171,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_106,c_164])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | ~ r1_tarski(k1_tarski(A_9),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_186,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_79),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_171,c_10])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_79),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_186,c_2])).

tff(c_218,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_193,plain,(
    ! [A_79] :
      ( m1_subset_1(A_79,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_79),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_186,c_14])).

tff(c_600,plain,(
    ! [A_120] :
      ( m1_subset_1(A_120,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_120),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_193])).

tff(c_604,plain,
    ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_557,c_600])).

tff(c_614,plain,(
    m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_604])).

tff(c_627,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_614])).

tff(c_635,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_627])).

tff(c_636,plain,(
    m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_635])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( k6_domain_1(A_21,B_22) = k1_tarski(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_642,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_636,c_34])).

tff(c_650,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_642])).

tff(c_60,plain,(
    ! [A_38,B_40] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_755,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_4')),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_60])).

tff(c_759,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_4')),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_636,c_755])).

tff(c_760,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_759])).

tff(c_764,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_760])).

tff(c_766,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_764])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_85,c_766])).

tff(c_785,plain,(
    ! [A_128] : ~ r1_tarski(k1_tarski(A_128),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_791,plain,(
    ! [A_129] : ~ r2_hidden(A_129,'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_785])).

tff(c_799,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_791])).

tff(c_806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_799])).

tff(c_807,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2419,plain,(
    ! [A_242,B_243] :
      ( m1_pre_topc('#skF_2'(A_242,B_243),A_242)
      | ~ v2_tex_2(B_243,A_242)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | v1_xboole_0(B_243)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2433,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2419])).

tff(c_2440,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_807,c_2433])).

tff(c_2441,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_64,c_2440])).

tff(c_30,plain,(
    ! [B_19,A_17] :
      ( l1_pre_topc(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2447,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2441,c_30])).

tff(c_2454,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2447])).

tff(c_28,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1847,plain,(
    ! [A_223,B_224] :
      ( ~ v2_struct_0('#skF_2'(A_223,B_224))
      | ~ v2_tex_2(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | v1_xboole_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1866,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1847])).

tff(c_1873,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_807,c_1866])).

tff(c_1874,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_64,c_1873])).

tff(c_68,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2444,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2441,c_46])).

tff(c_2450,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2444])).

tff(c_2451,plain,(
    v2_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2450])).

tff(c_38,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2458,plain,
    ( v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2451,c_38])).

tff(c_2460,plain,(
    v2_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_2458])).

tff(c_1645,plain,(
    ! [A_215,B_216] :
      ( v1_tdlat_3('#skF_2'(A_215,B_216))
      | ~ v2_tex_2(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | v1_xboole_0(B_216)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1664,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1645])).

tff(c_1671,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_807,c_1664])).

tff(c_1672,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_64,c_1671])).

tff(c_42,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_808,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2574,plain,(
    ! [A_246,B_247] :
      ( u1_struct_0('#skF_2'(A_246,B_247)) = B_247
      | ~ v2_tex_2(B_247,A_246)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | v1_xboole_0(B_247)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2597,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2574])).

tff(c_2605,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_807,c_2597])).

tff(c_2606,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_64,c_2605])).

tff(c_32,plain,(
    ! [A_20] :
      ( v1_zfmisc_1(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | ~ v7_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2627,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2606,c_32])).

tff(c_2648,plain,
    ( ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_808,c_2627])).

tff(c_2650,plain,(
    ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2648])).

tff(c_2653,plain,
    ( ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_2650])).

tff(c_2659,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_2460,c_1672,c_2451,c_2653])).

tff(c_2661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1874,c_2659])).

tff(c_2662,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2648])).

tff(c_2672,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_2662])).

tff(c_2676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_2672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.89  
% 4.62/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.89  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.62/1.89  
% 4.62/1.89  %Foreground sorts:
% 4.62/1.89  
% 4.62/1.89  
% 4.62/1.89  %Background operators:
% 4.62/1.89  
% 4.62/1.89  
% 4.62/1.89  %Foreground operators:
% 4.62/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.62/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.62/1.89  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.62/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.62/1.89  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.62/1.89  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.62/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.89  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.62/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.89  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.62/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.89  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.62/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.62/1.89  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.62/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.62/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.62/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.62/1.89  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.62/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.89  
% 4.62/1.91  tff(f_209, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 4.62/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.62/1.91  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.62/1.91  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.62/1.91  tff(f_148, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.62/1.91  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.62/1.91  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.62/1.91  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.62/1.91  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.62/1.91  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.62/1.91  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 4.62/1.91  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.62/1.91  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.62/1.91  tff(f_135, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 4.62/1.91  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 4.62/1.91  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 4.62/1.91  tff(f_84, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 4.62/1.91  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.91  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.62/1.91  tff(c_80, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_83, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 4.62/1.91  tff(c_74, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_85, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_74])).
% 4.62/1.91  tff(c_8, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.62/1.91  tff(c_251, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(A_89, B_88) | ~v1_zfmisc_1(B_88) | v1_xboole_0(B_88) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.62/1.91  tff(c_260, plain, (![A_9, B_10]: (k1_tarski(A_9)=B_10 | ~v1_zfmisc_1(B_10) | v1_xboole_0(B_10) | v1_xboole_0(k1_tarski(A_9)) | ~r2_hidden(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_251])).
% 4.62/1.91  tff(c_292, plain, (![A_91, B_92]: (k1_tarski(A_91)=B_92 | ~v1_zfmisc_1(B_92) | v1_xboole_0(B_92) | ~r2_hidden(A_91, B_92))), inference(negUnitSimplification, [status(thm)], [c_8, c_260])).
% 4.62/1.91  tff(c_305, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_292])).
% 4.62/1.91  tff(c_164, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/1.91  tff(c_242, plain, (![A_85, B_86, A_87]: (r1_tarski(A_85, B_86) | ~r1_tarski(A_85, k1_tarski(A_87)) | ~r2_hidden(A_87, B_86))), inference(resolution, [status(thm)], [c_12, c_164])).
% 4.62/1.91  tff(c_346, plain, (![A_98, B_99, A_100]: (r1_tarski(k1_tarski(A_98), B_99) | ~r2_hidden(A_100, B_99) | ~r2_hidden(A_98, k1_tarski(A_100)))), inference(resolution, [status(thm)], [c_12, c_242])).
% 4.62/1.91  tff(c_530, plain, (![A_117, A_118]: (r1_tarski(k1_tarski(A_117), A_118) | ~r2_hidden(A_117, k1_tarski('#skF_1'(A_118))) | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_4, c_346])).
% 4.62/1.91  tff(c_549, plain, (![A_118]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_118)))), A_118) | v1_xboole_0(A_118) | v1_xboole_0(k1_tarski('#skF_1'(A_118))))), inference(resolution, [status(thm)], [c_4, c_530])).
% 4.62/1.91  tff(c_557, plain, (![A_118]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_118)))), A_118) | v1_xboole_0(A_118))), inference(negUnitSimplification, [status(thm)], [c_8, c_549])).
% 4.62/1.91  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_102, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.62/1.91  tff(c_106, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_102])).
% 4.62/1.91  tff(c_171, plain, (![A_73]: (r1_tarski(A_73, u1_struct_0('#skF_3')) | ~r1_tarski(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_106, c_164])).
% 4.62/1.91  tff(c_10, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | ~r1_tarski(k1_tarski(A_9), B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.62/1.91  tff(c_186, plain, (![A_79]: (r2_hidden(A_79, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_79), '#skF_4'))), inference(resolution, [status(thm)], [c_171, c_10])).
% 4.62/1.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.91  tff(c_194, plain, (![A_79]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_79), '#skF_4'))), inference(resolution, [status(thm)], [c_186, c_2])).
% 4.62/1.91  tff(c_218, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_194])).
% 4.62/1.91  tff(c_14, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.62/1.91  tff(c_193, plain, (![A_79]: (m1_subset_1(A_79, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_79), '#skF_4'))), inference(resolution, [status(thm)], [c_186, c_14])).
% 4.62/1.91  tff(c_600, plain, (![A_120]: (m1_subset_1(A_120, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_120), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_218, c_193])).
% 4.62/1.91  tff(c_604, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_557, c_600])).
% 4.62/1.91  tff(c_614, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_604])).
% 4.62/1.91  tff(c_627, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_305, c_614])).
% 4.62/1.91  tff(c_635, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_627])).
% 4.62/1.91  tff(c_636, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_635])).
% 4.62/1.91  tff(c_34, plain, (![A_21, B_22]: (k6_domain_1(A_21, B_22)=k1_tarski(B_22) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.62/1.91  tff(c_642, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_34])).
% 4.62/1.91  tff(c_650, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_218, c_642])).
% 4.62/1.91  tff(c_60, plain, (![A_38, B_40]: (v2_tex_2(k6_domain_1(u1_struct_0(A_38), B_40), A_38) | ~m1_subset_1(B_40, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.62/1.91  tff(c_755, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_4')), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_650, c_60])).
% 4.62/1.91  tff(c_759, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_4')), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_636, c_755])).
% 4.62/1.91  tff(c_760, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_759])).
% 4.62/1.91  tff(c_764, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_305, c_760])).
% 4.62/1.91  tff(c_766, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_764])).
% 4.62/1.91  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_85, c_766])).
% 4.62/1.91  tff(c_785, plain, (![A_128]: (~r1_tarski(k1_tarski(A_128), '#skF_4'))), inference(splitRight, [status(thm)], [c_194])).
% 4.62/1.91  tff(c_791, plain, (![A_129]: (~r2_hidden(A_129, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_785])).
% 4.62/1.91  tff(c_799, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_791])).
% 4.62/1.91  tff(c_806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_799])).
% 4.62/1.91  tff(c_807, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 4.62/1.91  tff(c_2419, plain, (![A_242, B_243]: (m1_pre_topc('#skF_2'(A_242, B_243), A_242) | ~v2_tex_2(B_243, A_242) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | v1_xboole_0(B_243) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.62/1.91  tff(c_2433, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2419])).
% 4.62/1.91  tff(c_2440, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_807, c_2433])).
% 4.62/1.91  tff(c_2441, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_64, c_2440])).
% 4.62/1.91  tff(c_30, plain, (![B_19, A_17]: (l1_pre_topc(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.62/1.91  tff(c_2447, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2441, c_30])).
% 4.62/1.91  tff(c_2454, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2447])).
% 4.62/1.91  tff(c_28, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.62/1.91  tff(c_1847, plain, (![A_223, B_224]: (~v2_struct_0('#skF_2'(A_223, B_224)) | ~v2_tex_2(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | v1_xboole_0(B_224) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.62/1.91  tff(c_1866, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1847])).
% 4.62/1.91  tff(c_1873, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_807, c_1866])).
% 4.62/1.91  tff(c_1874, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_64, c_1873])).
% 4.62/1.91  tff(c_68, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.62/1.91  tff(c_46, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.62/1.91  tff(c_2444, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2441, c_46])).
% 4.62/1.91  tff(c_2450, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2444])).
% 4.62/1.91  tff(c_2451, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2450])).
% 4.62/1.91  tff(c_38, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.62/1.91  tff(c_2458, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2451, c_38])).
% 4.62/1.91  tff(c_2460, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_2458])).
% 4.62/1.91  tff(c_1645, plain, (![A_215, B_216]: (v1_tdlat_3('#skF_2'(A_215, B_216)) | ~v2_tex_2(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | v1_xboole_0(B_216) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.62/1.91  tff(c_1664, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1645])).
% 4.62/1.91  tff(c_1671, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_807, c_1664])).
% 4.62/1.91  tff(c_1672, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_64, c_1671])).
% 4.62/1.91  tff(c_42, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.62/1.91  tff(c_808, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 4.62/1.91  tff(c_2574, plain, (![A_246, B_247]: (u1_struct_0('#skF_2'(A_246, B_247))=B_247 | ~v2_tex_2(B_247, A_246) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | v1_xboole_0(B_247) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.62/1.91  tff(c_2597, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2574])).
% 4.62/1.91  tff(c_2605, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_807, c_2597])).
% 4.62/1.91  tff(c_2606, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_72, c_64, c_2605])).
% 4.62/1.91  tff(c_32, plain, (![A_20]: (v1_zfmisc_1(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | ~v7_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.91  tff(c_2627, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2606, c_32])).
% 4.62/1.91  tff(c_2648, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_808, c_2627])).
% 4.62/1.91  tff(c_2650, plain, (~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2648])).
% 4.62/1.91  tff(c_2653, plain, (~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_2650])).
% 4.62/1.91  tff(c_2659, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_2460, c_1672, c_2451, c_2653])).
% 4.62/1.91  tff(c_2661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1874, c_2659])).
% 4.62/1.91  tff(c_2662, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2648])).
% 4.62/1.91  tff(c_2672, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_2662])).
% 4.62/1.91  tff(c_2676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2454, c_2672])).
% 4.62/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.91  
% 4.62/1.91  Inference rules
% 4.62/1.91  ----------------------
% 4.62/1.91  #Ref     : 0
% 4.62/1.91  #Sup     : 561
% 4.62/1.91  #Fact    : 0
% 4.62/1.91  #Define  : 0
% 4.62/1.91  #Split   : 11
% 4.62/1.91  #Chain   : 0
% 4.62/1.91  #Close   : 0
% 4.62/1.91  
% 4.62/1.91  Ordering : KBO
% 4.62/1.91  
% 4.62/1.91  Simplification rules
% 4.62/1.91  ----------------------
% 4.62/1.91  #Subsume      : 162
% 4.62/1.91  #Demod        : 66
% 4.62/1.91  #Tautology    : 91
% 4.62/1.91  #SimpNegUnit  : 182
% 4.62/1.91  #BackRed      : 0
% 4.62/1.91  
% 4.62/1.91  #Partial instantiations: 0
% 4.62/1.91  #Strategies tried      : 1
% 4.62/1.91  
% 4.62/1.91  Timing (in seconds)
% 4.62/1.91  ----------------------
% 4.62/1.92  Preprocessing        : 0.41
% 4.62/1.92  Parsing              : 0.21
% 4.62/1.92  CNF conversion       : 0.03
% 4.62/1.92  Main loop            : 0.66
% 4.62/1.92  Inferencing          : 0.25
% 4.62/1.92  Reduction            : 0.18
% 4.62/1.92  Demodulation         : 0.11
% 4.62/1.92  BG Simplification    : 0.03
% 4.62/1.92  Subsumption          : 0.14
% 4.62/1.92  Abstraction          : 0.04
% 4.62/1.92  MUC search           : 0.00
% 4.62/1.92  Cooper               : 0.00
% 4.62/1.92  Total                : 1.12
% 4.62/1.92  Index Insertion      : 0.00
% 4.62/1.92  Index Deletion       : 0.00
% 4.62/1.92  Index Matching       : 0.00
% 4.62/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
