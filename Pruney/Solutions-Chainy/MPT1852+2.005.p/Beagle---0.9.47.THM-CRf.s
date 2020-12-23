%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:59 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 952 expanded)
%              Number of leaves         :   29 ( 330 expanded)
%              Depth                    :   25
%              Number of atoms          :  259 (2743 expanded)
%              Number of equality atoms :   12 ( 331 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_105,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_40,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_1'(A_39),u1_pre_topc(A_39))
      | v3_tdlat_3(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    ! [A_39] :
      ( m1_subset_1('#skF_1'(A_39),k1_zfmisc_1(u1_struct_0(A_39)))
      | v3_tdlat_3(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_34] :
      ( v1_tops_2(u1_pre_topc(A_34),A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_111,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc(A_70,g1_pre_topc(u1_struct_0(B_71),u1_pre_topc(B_71)))
      | ~ m1_pre_topc(A_70,B_71)
      | ~ l1_pre_topc(B_71)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_124,plain,(
    ! [A_70] :
      ( m1_pre_topc(A_70,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_70,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_111])).

tff(c_146,plain,(
    ! [A_75] :
      ( m1_pre_topc(A_75,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_75,'#skF_2')
      | ~ l1_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_124])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( m1_pre_topc(B_12,A_10)
      | ~ m1_pre_topc(B_12,g1_pre_topc(u1_struct_0(A_10),u1_pre_topc(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [A_75] :
      ( m1_pre_topc(A_75,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_75,'#skF_2')
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_146,c_14])).

tff(c_161,plain,(
    ! [A_76] :
      ( m1_pre_topc(A_76,'#skF_3')
      | ~ m1_pre_topc(A_76,'#skF_2')
      | ~ l1_pre_topc(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_152])).

tff(c_168,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_161])).

tff(c_172,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_168])).

tff(c_12,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [B_62,A_63] :
      ( m1_pre_topc(B_62,A_63)
      | ~ m1_pre_topc(B_62,g1_pre_topc(u1_struct_0(A_63),u1_pre_topc(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [B_62] :
      ( m1_pre_topc(B_62,'#skF_2')
      | ~ m1_pre_topc(B_62,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_88])).

tff(c_97,plain,(
    ! [B_62] :
      ( m1_pre_topc(B_62,'#skF_2')
      | ~ m1_pre_topc(B_62,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_91])).

tff(c_115,plain,(
    ! [A_70] :
      ( m1_pre_topc(A_70,'#skF_2')
      | ~ m1_pre_topc(A_70,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_111,c_97])).

tff(c_127,plain,(
    ! [A_70] :
      ( m1_pre_topc(A_70,'#skF_2')
      | ~ m1_pre_topc(A_70,'#skF_3')
      | ~ l1_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_115])).

tff(c_30,plain,(
    ! [B_38,A_36] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0(A_36))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_72,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(u1_struct_0(B_54),u1_struct_0(A_55))
      | ~ m1_pre_topc(B_54,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [B_79,A_80] :
      ( u1_struct_0(B_79) = u1_struct_0(A_80)
      | ~ r1_tarski(u1_struct_0(A_80),u1_struct_0(B_79))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_196,plain,(
    ! [B_81,A_82] :
      ( u1_struct_0(B_81) = u1_struct_0(A_82)
      | ~ m1_pre_topc(A_82,B_81)
      | ~ l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_198,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_172,c_196])).

tff(c_209,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_198])).

tff(c_217,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_220,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_217])).

tff(c_223,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_220])).

tff(c_226,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_226])).

tff(c_231,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_311,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_12])).

tff(c_336,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_311])).

tff(c_232,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_33,A_31] :
      ( v1_tops_2(B_33,A_31)
      | ~ r1_tarski(B_33,u1_pre_topc(A_31))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_287,plain,(
    ! [B_33] :
      ( v1_tops_2(B_33,'#skF_2')
      | ~ r1_tarski(B_33,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_22])).

tff(c_597,plain,(
    ! [B_100] :
      ( v1_tops_2(B_100,'#skF_2')
      | ~ r1_tarski(B_100,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_287])).

tff(c_600,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_336,c_597])).

tff(c_607,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_600])).

tff(c_24,plain,(
    ! [B_33,A_31] :
      ( r1_tarski(B_33,u1_pre_topc(A_31))
      | ~ v1_tops_2(B_33,A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_345,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_336,c_24])).

tff(c_353,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_345])).

tff(c_383,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_374,plain,(
    ! [D_87,C_88,A_89] :
      ( v1_tops_2(D_87,C_88)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_88))))
      | ~ v1_tops_2(D_87,A_89)
      | ~ m1_pre_topc(C_88,A_89)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_381,plain,(
    ! [A_89] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_89)
      | ~ m1_pre_topc('#skF_3',A_89)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_336,c_374])).

tff(c_722,plain,(
    ! [A_108] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_108)
      | ~ m1_pre_topc('#skF_3',A_108)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_108))))
      | ~ l1_pre_topc(A_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_383,c_381])).

tff(c_728,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_722])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_336,c_232,c_607,c_728])).

tff(c_739,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_773,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_739,c_2])).

tff(c_808,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_773])).

tff(c_284,plain,(
    ! [B_33] :
      ( r1_tarski(B_33,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_33,'#skF_2')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_24])).

tff(c_984,plain,(
    ! [B_119] :
      ( r1_tarski(B_119,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_119,'#skF_2')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_284])).

tff(c_991,plain,
    ( r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_984])).

tff(c_996,plain,
    ( r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_991])).

tff(c_997,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_808,c_996])).

tff(c_1047,plain,(
    ! [D_124,A_125] :
      ( v1_tops_2(D_124,'#skF_2')
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ v1_tops_2(D_124,A_125)
      | ~ m1_pre_topc('#skF_2',A_125)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_374])).

tff(c_1052,plain,(
    ! [A_125] :
      ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),A_125)
      | ~ m1_pre_topc('#skF_2',A_125)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_1047])).

tff(c_1057,plain,(
    ! [A_125] :
      ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),A_125)
      | ~ m1_pre_topc('#skF_2',A_125)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1052])).

tff(c_1067,plain,(
    ! [A_128] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_3'),A_128)
      | ~ m1_pre_topc('#skF_2',A_128)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128))))
      | ~ l1_pre_topc(A_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_1057])).

tff(c_1074,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1067])).

tff(c_1079,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_172,c_1074])).

tff(c_1082,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1079])).

tff(c_1086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1082])).

tff(c_1087,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    ! [A_39,B_42] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_39),B_42),u1_pre_topc(A_39))
      | ~ r2_hidden(B_42,u1_pre_topc(A_39))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ v3_tdlat_3(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_275,plain,(
    ! [B_42] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_42),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_42,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_32])).

tff(c_315,plain,(
    ! [B_42] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_42),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_42,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_231,c_275])).

tff(c_1470,plain,(
    ! [B_147] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_147),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_147,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1087,c_315])).

tff(c_34,plain,(
    ! [A_39] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_39),'#skF_1'(A_39)),u1_pre_topc(A_39))
      | v3_tdlat_3(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1478,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1470,c_34])).

tff(c_1483,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1478])).

tff(c_1484,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1483])).

tff(c_1496,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1484])).

tff(c_1505,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1496])).

tff(c_1512,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1505])).

tff(c_1514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1512])).

tff(c_1515,plain,(
    ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_1519,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1515])).

tff(c_1522,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1519])).

tff(c_1524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.73  
% 3.55/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.73  %$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.55/1.73  
% 3.55/1.73  %Foreground sorts:
% 3.55/1.73  
% 3.55/1.73  
% 3.55/1.73  %Background operators:
% 3.55/1.73  
% 3.55/1.73  
% 3.55/1.73  %Foreground operators:
% 3.55/1.73  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.55/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.73  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.55/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.55/1.73  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.55/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.55/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.73  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.55/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.73  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.55/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.55/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.73  
% 3.90/1.76  tff(f_128, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tex_2)).
% 3.90/1.76  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tdlat_3)).
% 3.90/1.76  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => v1_tops_2(u1_pre_topc(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_compts_1)).
% 3.90/1.76  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.90/1.76  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.90/1.76  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.90/1.76  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.90/1.76  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.90/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.90/1.76  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 3.90/1.76  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 3.90/1.76  tff(c_40, plain, (~v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.90/1.76  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.90/1.76  tff(c_36, plain, (![A_39]: (r2_hidden('#skF_1'(A_39), u1_pre_topc(A_39)) | v3_tdlat_3(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.90/1.76  tff(c_38, plain, (![A_39]: (m1_subset_1('#skF_1'(A_39), k1_zfmisc_1(u1_struct_0(A_39))) | v3_tdlat_3(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.90/1.76  tff(c_26, plain, (![A_34]: (v1_tops_2(u1_pre_topc(A_34), A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.90/1.76  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.90/1.76  tff(c_28, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.90/1.76  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.90/1.76  tff(c_111, plain, (![A_70, B_71]: (m1_pre_topc(A_70, g1_pre_topc(u1_struct_0(B_71), u1_pre_topc(B_71))) | ~m1_pre_topc(A_70, B_71) | ~l1_pre_topc(B_71) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.90/1.76  tff(c_124, plain, (![A_70]: (m1_pre_topc(A_70, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_70, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_70))), inference(superposition, [status(thm), theory('equality')], [c_44, c_111])).
% 3.90/1.76  tff(c_146, plain, (![A_75]: (m1_pre_topc(A_75, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_75, '#skF_2') | ~l1_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_124])).
% 3.90/1.76  tff(c_14, plain, (![B_12, A_10]: (m1_pre_topc(B_12, A_10) | ~m1_pre_topc(B_12, g1_pre_topc(u1_struct_0(A_10), u1_pre_topc(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.90/1.76  tff(c_152, plain, (![A_75]: (m1_pre_topc(A_75, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_75, '#skF_2') | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_146, c_14])).
% 3.90/1.76  tff(c_161, plain, (![A_76]: (m1_pre_topc(A_76, '#skF_3') | ~m1_pre_topc(A_76, '#skF_2') | ~l1_pre_topc(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_152])).
% 3.90/1.76  tff(c_168, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_161])).
% 3.90/1.76  tff(c_172, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_168])).
% 3.90/1.76  tff(c_12, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.90/1.76  tff(c_88, plain, (![B_62, A_63]: (m1_pre_topc(B_62, A_63) | ~m1_pre_topc(B_62, g1_pre_topc(u1_struct_0(A_63), u1_pre_topc(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.90/1.76  tff(c_91, plain, (![B_62]: (m1_pre_topc(B_62, '#skF_2') | ~m1_pre_topc(B_62, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_88])).
% 3.90/1.76  tff(c_97, plain, (![B_62]: (m1_pre_topc(B_62, '#skF_2') | ~m1_pre_topc(B_62, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_91])).
% 3.90/1.76  tff(c_115, plain, (![A_70]: (m1_pre_topc(A_70, '#skF_2') | ~m1_pre_topc(A_70, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_111, c_97])).
% 3.90/1.76  tff(c_127, plain, (![A_70]: (m1_pre_topc(A_70, '#skF_2') | ~m1_pre_topc(A_70, '#skF_3') | ~l1_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_115])).
% 3.90/1.76  tff(c_30, plain, (![B_38, A_36]: (r1_tarski(u1_struct_0(B_38), u1_struct_0(A_36)) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.90/1.76  tff(c_72, plain, (![B_54, A_55]: (r1_tarski(u1_struct_0(B_54), u1_struct_0(A_55)) | ~m1_pre_topc(B_54, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.90/1.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.76  tff(c_185, plain, (![B_79, A_80]: (u1_struct_0(B_79)=u1_struct_0(A_80) | ~r1_tarski(u1_struct_0(A_80), u1_struct_0(B_79)) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_72, c_2])).
% 3.90/1.76  tff(c_196, plain, (![B_81, A_82]: (u1_struct_0(B_81)=u1_struct_0(A_82) | ~m1_pre_topc(A_82, B_81) | ~l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_30, c_185])).
% 3.90/1.76  tff(c_198, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_172, c_196])).
% 3.90/1.76  tff(c_209, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_198])).
% 3.90/1.76  tff(c_217, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_209])).
% 3.90/1.76  tff(c_220, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_127, c_217])).
% 3.90/1.76  tff(c_223, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_220])).
% 3.90/1.76  tff(c_226, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_223])).
% 3.90/1.76  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_226])).
% 3.90/1.76  tff(c_231, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_209])).
% 3.90/1.76  tff(c_311, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_12])).
% 3.90/1.76  tff(c_336, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_311])).
% 3.90/1.76  tff(c_232, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_209])).
% 3.90/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.76  tff(c_22, plain, (![B_33, A_31]: (v1_tops_2(B_33, A_31) | ~r1_tarski(B_33, u1_pre_topc(A_31)) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31)))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.90/1.76  tff(c_287, plain, (![B_33]: (v1_tops_2(B_33, '#skF_2') | ~r1_tarski(B_33, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_22])).
% 3.90/1.76  tff(c_597, plain, (![B_100]: (v1_tops_2(B_100, '#skF_2') | ~r1_tarski(B_100, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_100, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_287])).
% 3.90/1.76  tff(c_600, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_336, c_597])).
% 3.90/1.76  tff(c_607, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_600])).
% 3.90/1.76  tff(c_24, plain, (![B_33, A_31]: (r1_tarski(B_33, u1_pre_topc(A_31)) | ~v1_tops_2(B_33, A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31)))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.90/1.76  tff(c_345, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_336, c_24])).
% 3.90/1.76  tff(c_353, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_345])).
% 3.90/1.76  tff(c_383, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_353])).
% 3.90/1.76  tff(c_374, plain, (![D_87, C_88, A_89]: (v1_tops_2(D_87, C_88) | ~m1_subset_1(D_87, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_88)))) | ~v1_tops_2(D_87, A_89) | ~m1_pre_topc(C_88, A_89) | ~m1_subset_1(D_87, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89)))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.90/1.76  tff(c_381, plain, (![A_89]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_89) | ~m1_pre_topc('#skF_3', A_89) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89)))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_336, c_374])).
% 3.90/1.76  tff(c_722, plain, (![A_108]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_108) | ~m1_pre_topc('#skF_3', A_108) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_108)))) | ~l1_pre_topc(A_108))), inference(negUnitSimplification, [status(thm)], [c_383, c_381])).
% 3.90/1.76  tff(c_728, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_722])).
% 3.90/1.76  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_336, c_232, c_607, c_728])).
% 3.90/1.76  tff(c_739, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_353])).
% 3.90/1.76  tff(c_773, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_739, c_2])).
% 3.90/1.76  tff(c_808, plain, (~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_773])).
% 3.90/1.76  tff(c_284, plain, (![B_33]: (r1_tarski(B_33, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_33, '#skF_2') | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_24])).
% 3.90/1.76  tff(c_984, plain, (![B_119]: (r1_tarski(B_119, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_119, '#skF_2') | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_284])).
% 3.90/1.76  tff(c_991, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_984])).
% 3.90/1.76  tff(c_996, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_991])).
% 3.90/1.76  tff(c_997, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_808, c_996])).
% 3.90/1.76  tff(c_1047, plain, (![D_124, A_125]: (v1_tops_2(D_124, '#skF_2') | ~m1_subset_1(D_124, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~v1_tops_2(D_124, A_125) | ~m1_pre_topc('#skF_2', A_125) | ~m1_subset_1(D_124, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125))), inference(superposition, [status(thm), theory('equality')], [c_231, c_374])).
% 3.90/1.76  tff(c_1052, plain, (![A_125]: (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_3'), A_125) | ~m1_pre_topc('#skF_2', A_125) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1047])).
% 3.90/1.76  tff(c_1057, plain, (![A_125]: (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_3'), A_125) | ~m1_pre_topc('#skF_2', A_125) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1052])).
% 3.90/1.76  tff(c_1067, plain, (![A_128]: (~v1_tops_2(u1_pre_topc('#skF_3'), A_128) | ~m1_pre_topc('#skF_2', A_128) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128)))) | ~l1_pre_topc(A_128))), inference(negUnitSimplification, [status(thm)], [c_997, c_1057])).
% 3.90/1.76  tff(c_1074, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1067])).
% 3.90/1.76  tff(c_1079, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_172, c_1074])).
% 3.90/1.76  tff(c_1082, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1079])).
% 3.90/1.76  tff(c_1086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1082])).
% 3.90/1.76  tff(c_1087, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_773])).
% 3.90/1.76  tff(c_42, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.90/1.76  tff(c_32, plain, (![A_39, B_42]: (r2_hidden(k6_subset_1(u1_struct_0(A_39), B_42), u1_pre_topc(A_39)) | ~r2_hidden(B_42, u1_pre_topc(A_39)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_39))) | ~v3_tdlat_3(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.90/1.76  tff(c_275, plain, (![B_42]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_42), u1_pre_topc('#skF_2')) | ~r2_hidden(B_42, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_32])).
% 3.90/1.76  tff(c_315, plain, (![B_42]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_42), u1_pre_topc('#skF_2')) | ~r2_hidden(B_42, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_231, c_275])).
% 3.90/1.76  tff(c_1470, plain, (![B_147]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_147), u1_pre_topc('#skF_3')) | ~r2_hidden(B_147, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1087, c_315])).
% 3.90/1.76  tff(c_34, plain, (![A_39]: (~r2_hidden(k6_subset_1(u1_struct_0(A_39), '#skF_1'(A_39)), u1_pre_topc(A_39)) | v3_tdlat_3(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.90/1.76  tff(c_1478, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1470, c_34])).
% 3.90/1.76  tff(c_1483, plain, (v3_tdlat_3('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1478])).
% 3.90/1.76  tff(c_1484, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1483])).
% 3.90/1.76  tff(c_1496, plain, (~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1484])).
% 3.90/1.76  tff(c_1505, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1496])).
% 3.90/1.76  tff(c_1512, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1505])).
% 3.90/1.76  tff(c_1514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1512])).
% 3.90/1.76  tff(c_1515, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_1484])).
% 3.90/1.76  tff(c_1519, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1515])).
% 3.90/1.76  tff(c_1522, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1519])).
% 3.90/1.76  tff(c_1524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1522])).
% 3.90/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.76  
% 3.90/1.76  Inference rules
% 3.90/1.76  ----------------------
% 3.90/1.76  #Ref     : 0
% 3.90/1.76  #Sup     : 264
% 3.90/1.76  #Fact    : 0
% 3.90/1.76  #Define  : 0
% 3.90/1.76  #Split   : 6
% 3.90/1.76  #Chain   : 0
% 3.90/1.76  #Close   : 0
% 3.90/1.76  
% 3.90/1.76  Ordering : KBO
% 3.90/1.76  
% 3.90/1.76  Simplification rules
% 3.90/1.76  ----------------------
% 3.90/1.76  #Subsume      : 89
% 3.90/1.76  #Demod        : 543
% 3.90/1.76  #Tautology    : 100
% 3.90/1.76  #SimpNegUnit  : 9
% 3.90/1.76  #BackRed      : 5
% 3.90/1.76  
% 3.90/1.76  #Partial instantiations: 0
% 3.90/1.76  #Strategies tried      : 1
% 3.90/1.76  
% 3.90/1.76  Timing (in seconds)
% 3.90/1.76  ----------------------
% 3.90/1.76  Preprocessing        : 0.37
% 3.90/1.76  Parsing              : 0.20
% 3.90/1.76  CNF conversion       : 0.03
% 3.90/1.76  Main loop            : 0.50
% 3.90/1.76  Inferencing          : 0.17
% 3.90/1.76  Reduction            : 0.17
% 3.90/1.76  Demodulation         : 0.13
% 3.90/1.76  BG Simplification    : 0.02
% 3.90/1.76  Subsumption          : 0.10
% 3.90/1.76  Abstraction          : 0.02
% 3.90/1.76  MUC search           : 0.00
% 3.90/1.76  Cooper               : 0.00
% 3.90/1.76  Total                : 0.92
% 3.90/1.76  Index Insertion      : 0.00
% 3.90/1.76  Index Deletion       : 0.00
% 3.90/1.76  Index Matching       : 0.00
% 3.90/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
