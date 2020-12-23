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
% DateTime   : Thu Dec  3 10:28:59 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :  143 (1717 expanded)
%              Number of leaves         :   30 ( 589 expanded)
%              Depth                    :   23
%              Number of atoms          :  371 (5181 expanded)
%              Number of equality atoms :   10 ( 582 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [A_41] :
      ( m1_pre_topc(A_41,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_119,plain,(
    ! [A_77,B_78] :
      ( m1_pre_topc(A_77,g1_pre_topc(u1_struct_0(B_78),u1_pre_topc(B_78)))
      | ~ m1_pre_topc(A_77,B_78)
      | ~ l1_pre_topc(B_78)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_132,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_77,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_119])).

tff(c_162,plain,(
    ! [A_85] :
      ( m1_pre_topc(A_85,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_85,'#skF_2')
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_132])).

tff(c_20,plain,(
    ! [B_22,A_20] :
      ( m1_pre_topc(B_22,A_20)
      | ~ m1_pre_topc(B_22,g1_pre_topc(u1_struct_0(A_20),u1_pre_topc(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_168,plain,(
    ! [A_85] :
      ( m1_pre_topc(A_85,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_85,'#skF_2')
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_162,c_20])).

tff(c_177,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,'#skF_3')
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_168])).

tff(c_184,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_177])).

tff(c_188,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_184])).

tff(c_86,plain,(
    ! [B_66,A_67] :
      ( m1_pre_topc(B_66,A_67)
      | ~ m1_pre_topc(B_66,g1_pre_topc(u1_struct_0(A_67),u1_pre_topc(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89,plain,(
    ! [B_66] :
      ( m1_pre_topc(B_66,'#skF_2')
      | ~ m1_pre_topc(B_66,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_86])).

tff(c_95,plain,(
    ! [B_66] :
      ( m1_pre_topc(B_66,'#skF_2')
      | ~ m1_pre_topc(B_66,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_89])).

tff(c_123,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,'#skF_2')
      | ~ m1_pre_topc(A_77,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_119,c_95])).

tff(c_135,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,'#skF_2')
      | ~ m1_pre_topc(A_77,'#skF_3')
      | ~ l1_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_123])).

tff(c_30,plain,(
    ! [B_44,A_42] :
      ( r1_tarski(u1_struct_0(B_44),u1_struct_0(A_42))
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(u1_struct_0(B_58),u1_struct_0(A_59))
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_195,plain,(
    ! [B_87,A_88] :
      ( u1_struct_0(B_87) = u1_struct_0(A_88)
      | ~ r1_tarski(u1_struct_0(A_88),u1_struct_0(B_87))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_206,plain,(
    ! [B_89,A_90] :
      ( u1_struct_0(B_89) = u1_struct_0(A_90)
      | ~ m1_pre_topc(A_90,B_89)
      | ~ l1_pre_topc(B_89)
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_208,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_188,c_206])).

tff(c_219,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_208])).

tff(c_227,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_237,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_227])).

tff(c_240,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_237])).

tff(c_243,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_243])).

tff(c_248,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_40,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    ! [A_45] :
      ( m1_subset_1('#skF_1'(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | v3_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_362,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(B_98)))
      | ~ m1_pre_topc(B_98,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1803,plain,(
    ! [C_193,A_194] :
      ( m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_2',A_194)
      | ~ l1_pre_topc(A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_362])).

tff(c_1819,plain,(
    ! [A_194] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_pre_topc('#skF_2',A_194)
      | ~ l1_pre_topc(A_194)
      | v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_1803])).

tff(c_1833,plain,(
    ! [A_194] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_pre_topc('#skF_2',A_194)
      | ~ l1_pre_topc(A_194)
      | v3_tdlat_3('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1819])).

tff(c_1835,plain,(
    ! [A_195] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_pre_topc('#skF_2',A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1833])).

tff(c_1854,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_1835])).

tff(c_1866,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1854])).

tff(c_1867,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1866])).

tff(c_1903,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_1867])).

tff(c_1910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_188,c_1903])).

tff(c_1911,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1866])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( r2_hidden(B_8,u1_pre_topc(A_6))
      | ~ v3_pre_topc(B_8,A_6)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_292,plain,(
    ! [B_8] :
      ( r2_hidden(B_8,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_8,'#skF_2')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_12])).

tff(c_469,plain,(
    ! [B_105] :
      ( r2_hidden(B_105,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_105,'#skF_2')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_292])).

tff(c_480,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_469])).

tff(c_487,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_480])).

tff(c_488,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_487])).

tff(c_517,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_924,plain,(
    ! [C_137,A_138] :
      ( m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_2',A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_362])).

tff(c_947,plain,(
    ! [A_138] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_pre_topc('#skF_2',A_138)
      | ~ l1_pre_topc(A_138)
      | v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_924])).

tff(c_966,plain,(
    ! [A_138] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_pre_topc('#skF_2',A_138)
      | ~ l1_pre_topc(A_138)
      | v3_tdlat_3('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_947])).

tff(c_968,plain,(
    ! [A_139] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_pre_topc('#skF_2',A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_966])).

tff(c_987,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_968])).

tff(c_999,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_987])).

tff(c_1001,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_999])).

tff(c_1004,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_1001])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_188,c_1004])).

tff(c_1013,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_1012,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_36,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),u1_pre_topc(A_45))
      | v3_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_16,plain,(
    ! [A_12] :
      ( m1_subset_1(u1_pre_topc(A_12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ! [A_60,C_61,B_62] :
      ( m1_subset_1(A_60,C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_60,A_12] :
      ( m1_subset_1(A_60,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ r2_hidden(A_60,u1_pre_topc(A_12))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_147,plain,(
    ! [B_80,A_81] :
      ( v3_pre_topc(B_80,A_81)
      | ~ r2_hidden(B_80,u1_pre_topc(A_81))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    ! [A_82,A_83] :
      ( v3_pre_topc(A_82,A_83)
      | ~ r2_hidden(A_82,u1_pre_topc(A_83))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_77,c_147])).

tff(c_160,plain,(
    ! [A_45] :
      ( v3_pre_topc('#skF_1'(A_45),A_45)
      | v3_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_36,c_156])).

tff(c_1063,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1012,c_12])).

tff(c_1072,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1063])).

tff(c_1075,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_1078,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_1075])).

tff(c_1081,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1078])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1081])).

tff(c_1085,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_26,plain,(
    ! [D_40,C_38,A_26] :
      ( v3_pre_topc(D_40,C_38)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0(C_38)))
      | ~ v3_pre_topc(D_40,A_26)
      | ~ m1_pre_topc(C_38,A_26)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1441,plain,(
    ! [A_174,A_175] :
      ( v3_pre_topc('#skF_1'('#skF_3'),A_174)
      | ~ v3_pre_topc('#skF_1'('#skF_3'),A_175)
      | ~ m1_pre_topc(A_174,A_175)
      | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175)
      | ~ m1_pre_topc('#skF_2',A_174)
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_968,c_26])).

tff(c_1451,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_188,c_1441])).

tff(c_1473,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1013,c_46,c_1012,c_1085,c_1451])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_1473])).

tff(c_1476,plain,(
    r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_489,plain,(
    ! [A_106,B_107] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_106),B_107),u1_pre_topc(A_106))
      | ~ r2_hidden(B_107,u1_pre_topc(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v3_tdlat_3(A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_507,plain,(
    ! [B_107] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_107),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_107,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_489])).

tff(c_2323,plain,(
    ! [B_234] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_234),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_234,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_248,c_507])).

tff(c_154,plain,(
    ! [A_60,A_12] :
      ( v3_pre_topc(A_60,A_12)
      | ~ r2_hidden(A_60,u1_pre_topc(A_12))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_77,c_147])).

tff(c_2335,plain,(
    ! [B_234] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_234),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(B_234,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_2323,c_154])).

tff(c_2346,plain,(
    ! [B_234] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_234),'#skF_2')
      | ~ r2_hidden(B_234,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2335])).

tff(c_32,plain,(
    ! [A_45,B_48] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_45),B_48),u1_pre_topc(A_45))
      | ~ r2_hidden(B_48,u1_pre_topc(A_45))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v3_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_301,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_60,u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_77])).

tff(c_328,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_60,u1_pre_topc('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_301])).

tff(c_1827,plain,(
    ! [A_60,A_194] :
      ( m1_subset_1(A_60,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_pre_topc('#skF_2',A_194)
      | ~ l1_pre_topc(A_194)
      | ~ r2_hidden(A_60,u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_328,c_1803])).

tff(c_249,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_1505,plain,(
    ! [D_176,C_177,A_178] :
      ( v3_pre_topc(D_176,C_177)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(u1_struct_0(C_177)))
      | ~ v3_pre_topc(D_176,A_178)
      | ~ m1_pre_topc(C_177,A_178)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3498,plain,(
    ! [A_323,A_324] :
      ( v3_pre_topc(A_323,'#skF_3')
      | ~ v3_pre_topc(A_323,A_324)
      | ~ m1_pre_topc('#skF_3',A_324)
      | ~ m1_subset_1(A_323,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324)
      | ~ r2_hidden(A_323,u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_328,c_1505])).

tff(c_3552,plain,(
    ! [A_323] :
      ( v3_pre_topc(A_323,'#skF_3')
      | ~ v3_pre_topc(A_323,'#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ m1_subset_1(A_323,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_323,u1_pre_topc('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_3498])).

tff(c_3623,plain,(
    ! [A_327] :
      ( v3_pre_topc(A_327,'#skF_3')
      | ~ v3_pre_topc(A_327,'#skF_2')
      | ~ m1_subset_1(A_327,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_327,u1_pre_topc('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_249,c_3552])).

tff(c_3650,plain,(
    ! [A_60] :
      ( v3_pre_topc(A_60,'#skF_3')
      | ~ v3_pre_topc(A_60,'#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_60,u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1827,c_3623])).

tff(c_3742,plain,(
    ! [A_328] :
      ( v3_pre_topc(A_328,'#skF_3')
      | ~ v3_pre_topc(A_328,'#skF_2')
      | ~ r2_hidden(A_328,u1_pre_topc('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_188,c_3650])).

tff(c_3773,plain,(
    ! [B_48] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_2'),B_48),'#skF_3')
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_2'),B_48),'#skF_2')
      | ~ r2_hidden(B_48,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_3742])).

tff(c_5881,plain,(
    ! [B_413] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_413),'#skF_3')
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_413),'#skF_2')
      | ~ r2_hidden(B_413,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_248,c_248,c_248,c_3773])).

tff(c_5885,plain,(
    ! [B_234] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_234),'#skF_3')
      | ~ r2_hidden(B_234,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_2346,c_5881])).

tff(c_352,plain,(
    ! [A_95] :
      ( m1_subset_1(A_95,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_95,u1_pre_topc('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_301])).

tff(c_355,plain,(
    ! [A_95] :
      ( r2_hidden(A_95,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_95,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_95,u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_352,c_12])).

tff(c_360,plain,(
    ! [A_95] :
      ( r2_hidden(A_95,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_95,'#skF_3')
      | ~ r2_hidden(A_95,u1_pre_topc('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_355])).

tff(c_493,plain,(
    ! [B_107] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_2'),B_107),u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_2'),B_107),'#skF_3')
      | ~ r2_hidden(B_107,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_489,c_360])).

tff(c_6062,plain,(
    ! [B_424] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_424),u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),B_424),'#skF_3')
      | ~ r2_hidden(B_424,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_248,c_248,c_248,c_493])).

tff(c_34,plain,(
    ! [A_45] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_45),'#skF_1'(A_45)),u1_pre_topc(A_45))
      | v3_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6097,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6062,c_34])).

tff(c_6120,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_1476,c_46,c_6097])).

tff(c_6121,plain,(
    ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_6120])).

tff(c_6124,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_5885,c_6121])).

tff(c_6131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_1476,c_6124])).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.07/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.57  
% 7.07/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.57  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 7.07/2.57  
% 7.07/2.57  %Foreground sorts:
% 7.07/2.57  
% 7.07/2.57  
% 7.07/2.57  %Background operators:
% 7.07/2.57  
% 7.07/2.57  
% 7.07/2.57  %Foreground operators:
% 7.07/2.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.07/2.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.07/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.07/2.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.07/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.07/2.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.07/2.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.07/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.07/2.57  tff('#skF_2', type, '#skF_2': $i).
% 7.07/2.57  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.07/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.07/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.07/2.57  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 7.07/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.07/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.07/2.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.07/2.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.07/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.07/2.57  
% 7.07/2.60  tff(f_134, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tex_2)).
% 7.07/2.60  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.07/2.60  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 7.07/2.60  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 7.07/2.60  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 7.07/2.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.07/2.60  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tdlat_3)).
% 7.07/2.60  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 7.07/2.60  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 7.07/2.60  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.07/2.60  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.07/2.60  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 7.07/2.60  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.07/2.60  tff(c_28, plain, (![A_41]: (m1_pre_topc(A_41, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.07/2.60  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.07/2.60  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.07/2.60  tff(c_119, plain, (![A_77, B_78]: (m1_pre_topc(A_77, g1_pre_topc(u1_struct_0(B_78), u1_pre_topc(B_78))) | ~m1_pre_topc(A_77, B_78) | ~l1_pre_topc(B_78) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.07/2.60  tff(c_132, plain, (![A_77]: (m1_pre_topc(A_77, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_77, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_77))), inference(superposition, [status(thm), theory('equality')], [c_44, c_119])).
% 7.07/2.60  tff(c_162, plain, (![A_85]: (m1_pre_topc(A_85, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_85, '#skF_2') | ~l1_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_132])).
% 7.07/2.60  tff(c_20, plain, (![B_22, A_20]: (m1_pre_topc(B_22, A_20) | ~m1_pre_topc(B_22, g1_pre_topc(u1_struct_0(A_20), u1_pre_topc(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.07/2.60  tff(c_168, plain, (![A_85]: (m1_pre_topc(A_85, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_85, '#skF_2') | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_162, c_20])).
% 7.07/2.60  tff(c_177, plain, (![A_86]: (m1_pre_topc(A_86, '#skF_3') | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_168])).
% 7.07/2.60  tff(c_184, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_177])).
% 7.07/2.60  tff(c_188, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_184])).
% 7.07/2.60  tff(c_86, plain, (![B_66, A_67]: (m1_pre_topc(B_66, A_67) | ~m1_pre_topc(B_66, g1_pre_topc(u1_struct_0(A_67), u1_pre_topc(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.07/2.60  tff(c_89, plain, (![B_66]: (m1_pre_topc(B_66, '#skF_2') | ~m1_pre_topc(B_66, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_86])).
% 7.07/2.60  tff(c_95, plain, (![B_66]: (m1_pre_topc(B_66, '#skF_2') | ~m1_pre_topc(B_66, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_89])).
% 7.07/2.60  tff(c_123, plain, (![A_77]: (m1_pre_topc(A_77, '#skF_2') | ~m1_pre_topc(A_77, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_119, c_95])).
% 7.07/2.60  tff(c_135, plain, (![A_77]: (m1_pre_topc(A_77, '#skF_2') | ~m1_pre_topc(A_77, '#skF_3') | ~l1_pre_topc(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_123])).
% 7.07/2.60  tff(c_30, plain, (![B_44, A_42]: (r1_tarski(u1_struct_0(B_44), u1_struct_0(A_42)) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.07/2.60  tff(c_70, plain, (![B_58, A_59]: (r1_tarski(u1_struct_0(B_58), u1_struct_0(A_59)) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.07/2.60  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.07/2.60  tff(c_195, plain, (![B_87, A_88]: (u1_struct_0(B_87)=u1_struct_0(A_88) | ~r1_tarski(u1_struct_0(A_88), u1_struct_0(B_87)) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_70, c_2])).
% 7.07/2.60  tff(c_206, plain, (![B_89, A_90]: (u1_struct_0(B_89)=u1_struct_0(A_90) | ~m1_pre_topc(A_90, B_89) | ~l1_pre_topc(B_89) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_30, c_195])).
% 7.07/2.60  tff(c_208, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_188, c_206])).
% 7.07/2.60  tff(c_219, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_208])).
% 7.07/2.60  tff(c_227, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_219])).
% 7.07/2.60  tff(c_237, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_135, c_227])).
% 7.07/2.60  tff(c_240, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_237])).
% 7.07/2.60  tff(c_243, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_240])).
% 7.07/2.60  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_243])).
% 7.07/2.60  tff(c_248, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_219])).
% 7.07/2.60  tff(c_40, plain, (~v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.07/2.60  tff(c_38, plain, (![A_45]: (m1_subset_1('#skF_1'(A_45), k1_zfmisc_1(u1_struct_0(A_45))) | v3_tdlat_3(A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.07/2.60  tff(c_362, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(B_98))) | ~m1_pre_topc(B_98, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.07/2.60  tff(c_1803, plain, (![C_193, A_194]: (m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', A_194) | ~l1_pre_topc(A_194))), inference(superposition, [status(thm), theory('equality')], [c_248, c_362])).
% 7.07/2.60  tff(c_1819, plain, (![A_194]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_pre_topc('#skF_2', A_194) | ~l1_pre_topc(A_194) | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_1803])).
% 7.07/2.60  tff(c_1833, plain, (![A_194]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_pre_topc('#skF_2', A_194) | ~l1_pre_topc(A_194) | v3_tdlat_3('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1819])).
% 7.07/2.60  tff(c_1835, plain, (![A_195]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_pre_topc('#skF_2', A_195) | ~l1_pre_topc(A_195))), inference(negUnitSimplification, [status(thm)], [c_40, c_1833])).
% 7.07/2.60  tff(c_1854, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_1835])).
% 7.07/2.60  tff(c_1866, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1854])).
% 7.07/2.60  tff(c_1867, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_1866])).
% 7.07/2.60  tff(c_1903, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_135, c_1867])).
% 7.07/2.60  tff(c_1910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_188, c_1903])).
% 7.07/2.60  tff(c_1911, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1866])).
% 7.07/2.60  tff(c_12, plain, (![B_8, A_6]: (r2_hidden(B_8, u1_pre_topc(A_6)) | ~v3_pre_topc(B_8, A_6) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.07/2.60  tff(c_292, plain, (![B_8]: (r2_hidden(B_8, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_8, '#skF_2') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_12])).
% 7.07/2.60  tff(c_469, plain, (![B_105]: (r2_hidden(B_105, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_105, '#skF_2') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_292])).
% 7.07/2.60  tff(c_480, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_469])).
% 7.07/2.60  tff(c_487, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_480])).
% 7.07/2.60  tff(c_488, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_487])).
% 7.07/2.60  tff(c_517, plain, (~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_488])).
% 7.07/2.60  tff(c_924, plain, (![C_137, A_138]: (m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', A_138) | ~l1_pre_topc(A_138))), inference(superposition, [status(thm), theory('equality')], [c_248, c_362])).
% 7.07/2.60  tff(c_947, plain, (![A_138]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_pre_topc('#skF_2', A_138) | ~l1_pre_topc(A_138) | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_924])).
% 7.07/2.60  tff(c_966, plain, (![A_138]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_pre_topc('#skF_2', A_138) | ~l1_pre_topc(A_138) | v3_tdlat_3('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_947])).
% 7.07/2.60  tff(c_968, plain, (![A_139]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_pre_topc('#skF_2', A_139) | ~l1_pre_topc(A_139))), inference(negUnitSimplification, [status(thm)], [c_40, c_966])).
% 7.07/2.60  tff(c_987, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_968])).
% 7.07/2.60  tff(c_999, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_987])).
% 7.07/2.60  tff(c_1001, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_999])).
% 7.07/2.60  tff(c_1004, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_135, c_1001])).
% 7.07/2.60  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_188, c_1004])).
% 7.07/2.60  tff(c_1013, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_999])).
% 7.07/2.60  tff(c_1012, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_999])).
% 7.07/2.60  tff(c_36, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), u1_pre_topc(A_45)) | v3_tdlat_3(A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.07/2.60  tff(c_16, plain, (![A_12]: (m1_subset_1(u1_pre_topc(A_12), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.07/2.60  tff(c_74, plain, (![A_60, C_61, B_62]: (m1_subset_1(A_60, C_61) | ~m1_subset_1(B_62, k1_zfmisc_1(C_61)) | ~r2_hidden(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.07/2.60  tff(c_77, plain, (![A_60, A_12]: (m1_subset_1(A_60, k1_zfmisc_1(u1_struct_0(A_12))) | ~r2_hidden(A_60, u1_pre_topc(A_12)) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_74])).
% 7.07/2.60  tff(c_147, plain, (![B_80, A_81]: (v3_pre_topc(B_80, A_81) | ~r2_hidden(B_80, u1_pre_topc(A_81)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.07/2.60  tff(c_156, plain, (![A_82, A_83]: (v3_pre_topc(A_82, A_83) | ~r2_hidden(A_82, u1_pre_topc(A_83)) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_77, c_147])).
% 7.07/2.60  tff(c_160, plain, (![A_45]: (v3_pre_topc('#skF_1'(A_45), A_45) | v3_tdlat_3(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_36, c_156])).
% 7.07/2.60  tff(c_1063, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1012, c_12])).
% 7.07/2.60  tff(c_1072, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1063])).
% 7.07/2.60  tff(c_1075, plain, (~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1072])).
% 7.07/2.60  tff(c_1078, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_160, c_1075])).
% 7.07/2.60  tff(c_1081, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1078])).
% 7.07/2.60  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1081])).
% 7.07/2.60  tff(c_1085, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1072])).
% 7.07/2.60  tff(c_26, plain, (![D_40, C_38, A_26]: (v3_pre_topc(D_40, C_38) | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0(C_38))) | ~v3_pre_topc(D_40, A_26) | ~m1_pre_topc(C_38, A_26) | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.07/2.60  tff(c_1441, plain, (![A_174, A_175]: (v3_pre_topc('#skF_1'('#skF_3'), A_174) | ~v3_pre_topc('#skF_1'('#skF_3'), A_175) | ~m1_pre_topc(A_174, A_175) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175) | ~m1_pre_topc('#skF_2', A_174) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_968, c_26])).
% 7.07/2.60  tff(c_1451, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_188, c_1441])).
% 7.07/2.60  tff(c_1473, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1013, c_46, c_1012, c_1085, c_1451])).
% 7.07/2.60  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_1473])).
% 7.07/2.60  tff(c_1476, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_488])).
% 7.07/2.60  tff(c_42, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.07/2.60  tff(c_489, plain, (![A_106, B_107]: (r2_hidden(k6_subset_1(u1_struct_0(A_106), B_107), u1_pre_topc(A_106)) | ~r2_hidden(B_107, u1_pre_topc(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~v3_tdlat_3(A_106) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.07/2.60  tff(c_507, plain, (![B_107]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_107), u1_pre_topc('#skF_2')) | ~r2_hidden(B_107, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_489])).
% 7.07/2.60  tff(c_2323, plain, (![B_234]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_234), u1_pre_topc('#skF_2')) | ~r2_hidden(B_234, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_248, c_507])).
% 7.07/2.60  tff(c_154, plain, (![A_60, A_12]: (v3_pre_topc(A_60, A_12) | ~r2_hidden(A_60, u1_pre_topc(A_12)) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_77, c_147])).
% 7.07/2.60  tff(c_2335, plain, (![B_234]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_234), '#skF_2') | ~l1_pre_topc('#skF_2') | ~r2_hidden(B_234, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_2323, c_154])).
% 7.07/2.60  tff(c_2346, plain, (![B_234]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_234), '#skF_2') | ~r2_hidden(B_234, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2335])).
% 7.07/2.60  tff(c_32, plain, (![A_45, B_48]: (r2_hidden(k6_subset_1(u1_struct_0(A_45), B_48), u1_pre_topc(A_45)) | ~r2_hidden(B_48, u1_pre_topc(A_45)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_45))) | ~v3_tdlat_3(A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.07/2.60  tff(c_301, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_60, u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_77])).
% 7.07/2.60  tff(c_328, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_60, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_301])).
% 7.07/2.60  tff(c_1827, plain, (![A_60, A_194]: (m1_subset_1(A_60, k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_pre_topc('#skF_2', A_194) | ~l1_pre_topc(A_194) | ~r2_hidden(A_60, u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_328, c_1803])).
% 7.07/2.60  tff(c_249, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_219])).
% 7.07/2.60  tff(c_1505, plain, (![D_176, C_177, A_178]: (v3_pre_topc(D_176, C_177) | ~m1_subset_1(D_176, k1_zfmisc_1(u1_struct_0(C_177))) | ~v3_pre_topc(D_176, A_178) | ~m1_pre_topc(C_177, A_178) | ~m1_subset_1(D_176, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.07/2.60  tff(c_3498, plain, (![A_323, A_324]: (v3_pre_topc(A_323, '#skF_3') | ~v3_pre_topc(A_323, A_324) | ~m1_pre_topc('#skF_3', A_324) | ~m1_subset_1(A_323, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324) | ~r2_hidden(A_323, u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_328, c_1505])).
% 7.07/2.60  tff(c_3552, plain, (![A_323]: (v3_pre_topc(A_323, '#skF_3') | ~v3_pre_topc(A_323, '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(A_323, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_323, u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_248, c_3498])).
% 7.07/2.60  tff(c_3623, plain, (![A_327]: (v3_pre_topc(A_327, '#skF_3') | ~v3_pre_topc(A_327, '#skF_2') | ~m1_subset_1(A_327, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_327, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_249, c_3552])).
% 7.07/2.60  tff(c_3650, plain, (![A_60]: (v3_pre_topc(A_60, '#skF_3') | ~v3_pre_topc(A_60, '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_60, u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_1827, c_3623])).
% 7.07/2.60  tff(c_3742, plain, (![A_328]: (v3_pre_topc(A_328, '#skF_3') | ~v3_pre_topc(A_328, '#skF_2') | ~r2_hidden(A_328, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_188, c_3650])).
% 7.07/2.60  tff(c_3773, plain, (![B_48]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_2'), B_48), '#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_2'), B_48), '#skF_2') | ~r2_hidden(B_48, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_3742])).
% 7.07/2.60  tff(c_5881, plain, (![B_413]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_413), '#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_413), '#skF_2') | ~r2_hidden(B_413, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_248, c_248, c_248, c_3773])).
% 7.07/2.60  tff(c_5885, plain, (![B_234]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_234), '#skF_3') | ~r2_hidden(B_234, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_2346, c_5881])).
% 7.07/2.60  tff(c_352, plain, (![A_95]: (m1_subset_1(A_95, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_95, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_301])).
% 7.07/2.60  tff(c_355, plain, (![A_95]: (r2_hidden(A_95, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_95, '#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_95, u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_352, c_12])).
% 7.07/2.60  tff(c_360, plain, (![A_95]: (r2_hidden(A_95, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_95, '#skF_3') | ~r2_hidden(A_95, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_355])).
% 7.07/2.60  tff(c_493, plain, (![B_107]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_2'), B_107), u1_pre_topc('#skF_3')) | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_2'), B_107), '#skF_3') | ~r2_hidden(B_107, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_489, c_360])).
% 7.07/2.60  tff(c_6062, plain, (![B_424]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_424), u1_pre_topc('#skF_3')) | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), B_424), '#skF_3') | ~r2_hidden(B_424, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_424, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_248, c_248, c_248, c_493])).
% 7.07/2.60  tff(c_34, plain, (![A_45]: (~r2_hidden(k6_subset_1(u1_struct_0(A_45), '#skF_1'(A_45)), u1_pre_topc(A_45)) | v3_tdlat_3(A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.07/2.60  tff(c_6097, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6062, c_34])).
% 7.07/2.60  tff(c_6120, plain, (v3_tdlat_3('#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_1476, c_46, c_6097])).
% 7.07/2.60  tff(c_6121, plain, (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_6120])).
% 7.07/2.60  tff(c_6124, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5885, c_6121])).
% 7.07/2.60  tff(c_6131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1911, c_1476, c_6124])).
% 7.07/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.60  
% 7.07/2.60  Inference rules
% 7.07/2.60  ----------------------
% 7.07/2.60  #Ref     : 0
% 7.07/2.60  #Sup     : 1263
% 7.07/2.60  #Fact    : 0
% 7.07/2.60  #Define  : 0
% 7.07/2.60  #Split   : 17
% 7.07/2.60  #Chain   : 0
% 7.07/2.60  #Close   : 0
% 7.07/2.60  
% 7.07/2.60  Ordering : KBO
% 7.07/2.60  
% 7.07/2.60  Simplification rules
% 7.07/2.60  ----------------------
% 7.07/2.60  #Subsume      : 460
% 7.07/2.60  #Demod        : 1642
% 7.07/2.60  #Tautology    : 271
% 7.07/2.60  #SimpNegUnit  : 52
% 7.07/2.60  #BackRed      : 1
% 7.07/2.60  
% 7.07/2.60  #Partial instantiations: 0
% 7.07/2.60  #Strategies tried      : 1
% 7.07/2.60  
% 7.07/2.60  Timing (in seconds)
% 7.07/2.60  ----------------------
% 7.35/2.60  Preprocessing        : 0.35
% 7.35/2.60  Parsing              : 0.19
% 7.35/2.60  CNF conversion       : 0.03
% 7.35/2.60  Main loop            : 1.39
% 7.35/2.60  Inferencing          : 0.42
% 7.35/2.60  Reduction            : 0.42
% 7.35/2.60  Demodulation         : 0.29
% 7.35/2.60  BG Simplification    : 0.04
% 7.35/2.60  Subsumption          : 0.42
% 7.35/2.60  Abstraction          : 0.06
% 7.35/2.60  MUC search           : 0.00
% 7.35/2.60  Cooper               : 0.00
% 7.35/2.60  Total                : 1.80
% 7.35/2.60  Index Insertion      : 0.00
% 7.35/2.60  Index Deletion       : 0.00
% 7.35/2.60  Index Matching       : 0.00
% 7.35/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
