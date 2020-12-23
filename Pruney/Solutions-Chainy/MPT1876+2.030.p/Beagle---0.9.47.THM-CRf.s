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
% DateTime   : Thu Dec  3 10:29:54 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 448 expanded)
%              Number of leaves         :   43 ( 174 expanded)
%              Depth                    :   19
%              Number of atoms          :  299 (1512 expanded)
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

tff(f_194,negated_conjecture,(
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

tff(f_133,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_162,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_106,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

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

tff(c_72,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_78,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66])).

tff(c_8,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_200,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(A_76,B_75)
      | ~ v1_zfmisc_1(B_75)
      | v1_xboole_0(B_75)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_209,plain,(
    ! [A_9,B_10] :
      ( k1_tarski(A_9) = B_10
      | ~ v1_zfmisc_1(B_10)
      | v1_xboole_0(B_10)
      | v1_xboole_0(k1_tarski(A_9))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_251,plain,(
    ! [A_78,B_79] :
      ( k1_tarski(A_78) = B_79
      | ~ v1_zfmisc_1(B_79)
      | v1_xboole_0(B_79)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_209])).

tff(c_260,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_251])).

tff(c_122,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(B_65,C_64)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_289,plain,(
    ! [A_82,B_83,A_84] :
      ( r1_tarski(A_82,B_83)
      | ~ r1_tarski(A_82,k1_tarski(A_84))
      | ~ r2_hidden(A_84,B_83) ) ),
    inference(resolution,[status(thm)],[c_12,c_122])).

tff(c_300,plain,(
    ! [A_85,B_86,A_87] :
      ( r1_tarski(k1_tarski(A_85),B_86)
      | ~ r2_hidden(A_87,B_86)
      | ~ r2_hidden(A_85,k1_tarski(A_87)) ) ),
    inference(resolution,[status(thm)],[c_12,c_289])).

tff(c_456,plain,(
    ! [A_104,A_105] :
      ( r1_tarski(k1_tarski(A_104),A_105)
      | ~ r2_hidden(A_104,k1_tarski('#skF_1'(A_105)))
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_300])).

tff(c_471,plain,(
    ! [A_105] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_105)))),A_105)
      | v1_xboole_0(A_105)
      | v1_xboole_0(k1_tarski('#skF_1'(A_105))) ) ),
    inference(resolution,[status(thm)],[c_4,c_456])).

tff(c_477,plain,(
    ! [A_106] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_106)))),A_106)
      | v1_xboole_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_471])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_101,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_132,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_114,c_122])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | ~ r1_tarski(k1_tarski(A_9),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141,plain,(
    ! [A_67] :
      ( r2_hidden(A_67,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_67),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_10])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_67),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_141,c_14])).

tff(c_494,plain,
    ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_477,c_148])).

tff(c_520,plain,(
    m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_494])).

tff(c_530,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_520])).

tff(c_535,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_530])).

tff(c_536,plain,(
    m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_535])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_67),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_150,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_539,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_536,c_26])).

tff(c_542,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_539])).

tff(c_52,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_605,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_4')),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_52])).

tff(c_615,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_4')),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_536,c_605])).

tff(c_616,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_615])).

tff(c_622,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_616])).

tff(c_624,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_622])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_78,c_624])).

tff(c_643,plain,(
    ! [A_113] : ~ r1_tarski(k1_tarski(A_113),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_649,plain,(
    ! [A_114] : ~ r2_hidden(A_114,'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_643])).

tff(c_653,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_649])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_653])).

tff(c_658,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2064,plain,(
    ! [A_213,B_214] :
      ( m1_pre_topc('#skF_2'(A_213,B_214),A_213)
      | ~ v2_tex_2(B_214,A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | v1_xboole_0(B_214)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2081,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2064])).

tff(c_2089,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_658,c_2081])).

tff(c_2090,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_2089])).

tff(c_22,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2096,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2090,c_22])).

tff(c_2103,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2096])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1360,plain,(
    ! [A_182,B_183] :
      ( ~ v2_struct_0('#skF_2'(A_182,B_183))
      | ~ v2_tex_2(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | v1_xboole_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1375,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1360])).

tff(c_1381,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_658,c_1375])).

tff(c_1382,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_1381])).

tff(c_60,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_38,plain,(
    ! [B_27,A_25] :
      ( v2_tdlat_3(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2093,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2090,c_38])).

tff(c_2099,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2093])).

tff(c_2100,plain,(
    v2_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2099])).

tff(c_30,plain,(
    ! [A_23] :
      ( v2_pre_topc(A_23)
      | ~ v2_tdlat_3(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2107,plain,
    ( v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2100,c_30])).

tff(c_2109,plain,(
    v2_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2107])).

tff(c_1806,plain,(
    ! [A_206,B_207] :
      ( v1_tdlat_3('#skF_2'(A_206,B_207))
      | ~ v2_tex_2(B_207,A_206)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | v1_xboole_0(B_207)
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1825,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1806])).

tff(c_1832,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_658,c_1825])).

tff(c_1833,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_1832])).

tff(c_34,plain,(
    ! [A_24] :
      ( v7_struct_0(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ v1_tdlat_3(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_659,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2252,plain,(
    ! [A_218,B_219] :
      ( u1_struct_0('#skF_2'(A_218,B_219)) = B_219
      | ~ v2_tex_2(B_219,A_218)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | v1_xboole_0(B_219)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2279,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2252])).

tff(c_2288,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_658,c_2279])).

tff(c_2289,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_2288])).

tff(c_24,plain,(
    ! [A_19] :
      ( v1_zfmisc_1(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | ~ v7_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2310,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_24])).

tff(c_2331,plain,
    ( ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_659,c_2310])).

tff(c_2333,plain,(
    ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2331])).

tff(c_2336,plain,
    ( ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_2333])).

tff(c_2339,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2109,c_1833,c_2100,c_2336])).

tff(c_2341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1382,c_2339])).

tff(c_2342,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2331])).

tff(c_2352,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_2342])).

tff(c_2356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.85  
% 4.81/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.86  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.81/1.86  
% 4.81/1.86  %Foreground sorts:
% 4.81/1.86  
% 4.81/1.86  
% 4.81/1.86  %Background operators:
% 4.81/1.86  
% 4.81/1.86  
% 4.81/1.86  %Foreground operators:
% 4.81/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.81/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.81/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.81/1.86  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.81/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.81/1.86  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.81/1.86  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.81/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.86  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.81/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.86  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.81/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.81/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.81/1.86  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.81/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.81/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.81/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.81/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.81/1.86  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.81/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.86  
% 4.81/1.89  tff(f_194, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 4.81/1.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.81/1.89  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.81/1.89  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.81/1.89  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.81/1.89  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.81/1.89  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.81/1.89  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.81/1.89  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.81/1.89  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.81/1.89  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 4.81/1.89  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.81/1.89  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.81/1.89  tff(f_120, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 4.81/1.89  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 4.81/1.89  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 4.81/1.89  tff(f_69, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 4.81/1.89  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.89  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.81/1.89  tff(c_72, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_76, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 4.81/1.89  tff(c_66, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_78, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66])).
% 4.81/1.89  tff(c_8, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.81/1.89  tff(c_200, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(A_76, B_75) | ~v1_zfmisc_1(B_75) | v1_xboole_0(B_75) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.81/1.89  tff(c_209, plain, (![A_9, B_10]: (k1_tarski(A_9)=B_10 | ~v1_zfmisc_1(B_10) | v1_xboole_0(B_10) | v1_xboole_0(k1_tarski(A_9)) | ~r2_hidden(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_200])).
% 4.81/1.89  tff(c_251, plain, (![A_78, B_79]: (k1_tarski(A_78)=B_79 | ~v1_zfmisc_1(B_79) | v1_xboole_0(B_79) | ~r2_hidden(A_78, B_79))), inference(negUnitSimplification, [status(thm)], [c_8, c_209])).
% 4.81/1.89  tff(c_260, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_251])).
% 4.81/1.89  tff(c_122, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(B_65, C_64) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.81/1.89  tff(c_289, plain, (![A_82, B_83, A_84]: (r1_tarski(A_82, B_83) | ~r1_tarski(A_82, k1_tarski(A_84)) | ~r2_hidden(A_84, B_83))), inference(resolution, [status(thm)], [c_12, c_122])).
% 4.81/1.89  tff(c_300, plain, (![A_85, B_86, A_87]: (r1_tarski(k1_tarski(A_85), B_86) | ~r2_hidden(A_87, B_86) | ~r2_hidden(A_85, k1_tarski(A_87)))), inference(resolution, [status(thm)], [c_12, c_289])).
% 4.81/1.89  tff(c_456, plain, (![A_104, A_105]: (r1_tarski(k1_tarski(A_104), A_105) | ~r2_hidden(A_104, k1_tarski('#skF_1'(A_105))) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_4, c_300])).
% 4.81/1.89  tff(c_471, plain, (![A_105]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_105)))), A_105) | v1_xboole_0(A_105) | v1_xboole_0(k1_tarski('#skF_1'(A_105))))), inference(resolution, [status(thm)], [c_4, c_456])).
% 4.81/1.89  tff(c_477, plain, (![A_106]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_106)))), A_106) | v1_xboole_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_8, c_471])).
% 4.81/1.89  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_101, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.81/1.89  tff(c_114, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_101])).
% 4.81/1.89  tff(c_132, plain, (![A_66]: (r1_tarski(A_66, u1_struct_0('#skF_3')) | ~r1_tarski(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_114, c_122])).
% 4.81/1.89  tff(c_10, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | ~r1_tarski(k1_tarski(A_9), B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.81/1.89  tff(c_141, plain, (![A_67]: (r2_hidden(A_67, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_67), '#skF_4'))), inference(resolution, [status(thm)], [c_132, c_10])).
% 4.81/1.89  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.81/1.89  tff(c_148, plain, (![A_67]: (m1_subset_1(A_67, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_67), '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_14])).
% 4.81/1.89  tff(c_494, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_477, c_148])).
% 4.81/1.89  tff(c_520, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_494])).
% 4.81/1.89  tff(c_530, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_260, c_520])).
% 4.81/1.89  tff(c_535, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_530])).
% 4.81/1.89  tff(c_536, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_535])).
% 4.81/1.89  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.89  tff(c_149, plain, (![A_67]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_67), '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_2])).
% 4.81/1.89  tff(c_150, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_149])).
% 4.81/1.89  tff(c_26, plain, (![A_20, B_21]: (k6_domain_1(A_20, B_21)=k1_tarski(B_21) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.81/1.89  tff(c_539, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_536, c_26])).
% 4.81/1.89  tff(c_542, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_150, c_539])).
% 4.81/1.89  tff(c_52, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.81/1.89  tff(c_605, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_4')), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_542, c_52])).
% 4.81/1.89  tff(c_615, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_4')), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_536, c_605])).
% 4.81/1.89  tff(c_616, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_615])).
% 4.81/1.89  tff(c_622, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_260, c_616])).
% 4.81/1.89  tff(c_624, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_622])).
% 4.81/1.89  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_78, c_624])).
% 4.81/1.89  tff(c_643, plain, (![A_113]: (~r1_tarski(k1_tarski(A_113), '#skF_4'))), inference(splitRight, [status(thm)], [c_149])).
% 4.81/1.89  tff(c_649, plain, (![A_114]: (~r2_hidden(A_114, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_643])).
% 4.81/1.89  tff(c_653, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_649])).
% 4.81/1.89  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_653])).
% 4.81/1.89  tff(c_658, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_72])).
% 4.81/1.89  tff(c_2064, plain, (![A_213, B_214]: (m1_pre_topc('#skF_2'(A_213, B_214), A_213) | ~v2_tex_2(B_214, A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | v1_xboole_0(B_214) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.81/1.89  tff(c_2081, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2064])).
% 4.81/1.89  tff(c_2089, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_658, c_2081])).
% 4.81/1.89  tff(c_2090, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_2089])).
% 4.81/1.89  tff(c_22, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.81/1.89  tff(c_2096, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2090, c_22])).
% 4.81/1.89  tff(c_2103, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2096])).
% 4.81/1.89  tff(c_20, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.81/1.89  tff(c_1360, plain, (![A_182, B_183]: (~v2_struct_0('#skF_2'(A_182, B_183)) | ~v2_tex_2(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | v1_xboole_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.81/1.89  tff(c_1375, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1360])).
% 4.81/1.89  tff(c_1381, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_658, c_1375])).
% 4.81/1.89  tff(c_1382, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_1381])).
% 4.81/1.89  tff(c_60, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.81/1.89  tff(c_38, plain, (![B_27, A_25]: (v2_tdlat_3(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.81/1.89  tff(c_2093, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2090, c_38])).
% 4.81/1.89  tff(c_2099, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2093])).
% 4.81/1.89  tff(c_2100, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_2099])).
% 4.81/1.89  tff(c_30, plain, (![A_23]: (v2_pre_topc(A_23) | ~v2_tdlat_3(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.81/1.89  tff(c_2107, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2100, c_30])).
% 4.81/1.89  tff(c_2109, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2107])).
% 4.81/1.89  tff(c_1806, plain, (![A_206, B_207]: (v1_tdlat_3('#skF_2'(A_206, B_207)) | ~v2_tex_2(B_207, A_206) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_206))) | v1_xboole_0(B_207) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.81/1.89  tff(c_1825, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1806])).
% 4.81/1.89  tff(c_1832, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_658, c_1825])).
% 4.81/1.89  tff(c_1833, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_1832])).
% 4.81/1.89  tff(c_34, plain, (![A_24]: (v7_struct_0(A_24) | ~v2_tdlat_3(A_24) | ~v1_tdlat_3(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.81/1.89  tff(c_659, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 4.81/1.89  tff(c_2252, plain, (![A_218, B_219]: (u1_struct_0('#skF_2'(A_218, B_219))=B_219 | ~v2_tex_2(B_219, A_218) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | v1_xboole_0(B_219) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.81/1.89  tff(c_2279, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2252])).
% 4.81/1.89  tff(c_2288, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_658, c_2279])).
% 4.81/1.89  tff(c_2289, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_2288])).
% 4.81/1.89  tff(c_24, plain, (![A_19]: (v1_zfmisc_1(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | ~v7_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.81/1.89  tff(c_2310, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2289, c_24])).
% 4.81/1.89  tff(c_2331, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_659, c_2310])).
% 4.81/1.89  tff(c_2333, plain, (~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2331])).
% 4.81/1.89  tff(c_2336, plain, (~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_2333])).
% 4.81/1.89  tff(c_2339, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2109, c_1833, c_2100, c_2336])).
% 4.81/1.89  tff(c_2341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1382, c_2339])).
% 4.81/1.89  tff(c_2342, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2331])).
% 4.81/1.89  tff(c_2352, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_2342])).
% 4.81/1.89  tff(c_2356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2352])).
% 4.81/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.89  
% 4.81/1.89  Inference rules
% 4.81/1.89  ----------------------
% 4.81/1.89  #Ref     : 0
% 4.81/1.89  #Sup     : 497
% 4.81/1.89  #Fact    : 0
% 4.81/1.89  #Define  : 0
% 4.81/1.89  #Split   : 11
% 4.81/1.89  #Chain   : 0
% 4.81/1.89  #Close   : 0
% 4.81/1.89  
% 4.81/1.89  Ordering : KBO
% 4.81/1.89  
% 4.81/1.89  Simplification rules
% 4.81/1.89  ----------------------
% 4.81/1.89  #Subsume      : 131
% 4.81/1.89  #Demod        : 66
% 4.81/1.89  #Tautology    : 69
% 4.81/1.89  #SimpNegUnit  : 155
% 4.81/1.89  #BackRed      : 0
% 4.81/1.89  
% 4.81/1.89  #Partial instantiations: 0
% 4.81/1.89  #Strategies tried      : 1
% 4.81/1.89  
% 4.81/1.89  Timing (in seconds)
% 4.81/1.89  ----------------------
% 4.81/1.90  Preprocessing        : 0.35
% 4.81/1.90  Parsing              : 0.18
% 4.81/1.90  CNF conversion       : 0.03
% 4.81/1.90  Main loop            : 0.72
% 4.81/1.90  Inferencing          : 0.26
% 4.81/1.90  Reduction            : 0.20
% 4.81/1.90  Demodulation         : 0.12
% 4.81/1.90  BG Simplification    : 0.03
% 4.81/1.90  Subsumption          : 0.16
% 4.81/1.90  Abstraction          : 0.04
% 4.81/1.90  MUC search           : 0.00
% 4.81/1.90  Cooper               : 0.00
% 4.81/1.90  Total                : 1.14
% 4.81/1.90  Index Insertion      : 0.00
% 4.81/1.90  Index Deletion       : 0.00
% 4.81/1.90  Index Matching       : 0.00
% 4.81/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
