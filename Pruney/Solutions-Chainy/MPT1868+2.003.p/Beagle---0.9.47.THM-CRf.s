%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:35 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 212 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 ( 588 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_196,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & v2_pre_topc(B) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & v2_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_183,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_272,plain,(
    ! [A_88,B_89] :
      ( m1_pre_topc(k1_tex_2(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_277,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_272])).

tff(c_281,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_277])).

tff(c_282,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_281])).

tff(c_257,plain,(
    ! [A_84,B_85] :
      ( ~ v2_struct_0(k1_tex_2(A_84,B_85))
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_264,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_257])).

tff(c_268,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_264])).

tff(c_269,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_268])).

tff(c_231,plain,(
    ! [A_80,B_81] :
      ( v7_struct_0(k1_tex_2(A_80,B_81))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_238,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_231])).

tff(c_242,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_238])).

tff(c_243,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_242])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_16,plain,(
    ! [B_10,A_8] :
      ( v2_pre_topc(B_10)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_285,plain,
    ( v2_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_16])).

tff(c_288,plain,(
    v2_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_285])).

tff(c_330,plain,(
    ! [B_103,A_104] :
      ( v1_tdlat_3(B_103)
      | ~ v2_pre_topc(B_103)
      | ~ v7_struct_0(B_103)
      | v2_struct_0(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_333,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_330])).

tff(c_336,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_243,c_288,c_333])).

tff(c_337,plain,(
    v1_tdlat_3(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_269,c_336])).

tff(c_244,plain,(
    ! [A_82,B_83] :
      ( v1_pre_topc(k1_tex_2(A_82,B_83))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_251,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_244])).

tff(c_255,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_251])).

tff(c_256,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_255])).

tff(c_69,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_69])).

tff(c_78,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_154,plain,(
    ! [A_69,B_70] :
      ( k6_domain_1(A_69,B_70) = k1_tarski(B_70)
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_163,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_154])).

tff(c_168,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_163])).

tff(c_470,plain,(
    ! [A_127,B_128] :
      ( k6_domain_1(u1_struct_0(A_127),B_128) = u1_struct_0(k1_tex_2(A_127,B_128))
      | ~ m1_pre_topc(k1_tex_2(A_127,B_128),A_127)
      | ~ v1_pre_topc(k1_tex_2(A_127,B_128))
      | v2_struct_0(k1_tex_2(A_127,B_128))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_474,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_470])).

tff(c_478,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = k1_tarski('#skF_3')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_256,c_168,c_474])).

tff(c_479,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_269,c_478])).

tff(c_50,plain,(
    ! [B_33,A_31] :
      ( m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_358,plain,(
    ! [B_109,A_110] :
      ( v2_tex_2(u1_struct_0(B_109),A_110)
      | ~ v1_tdlat_3(B_109)
      | ~ m1_subset_1(u1_struct_0(B_109),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_pre_topc(B_109,A_110)
      | v2_struct_0(B_109)
      | ~ l1_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_369,plain,(
    ! [B_33,A_31] :
      ( v2_tex_2(u1_struct_0(B_33),A_31)
      | ~ v1_tdlat_3(B_33)
      | v2_struct_0(B_33)
      | v2_struct_0(A_31)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_50,c_358])).

tff(c_497,plain,(
    ! [A_31] :
      ( v2_tex_2(k1_tarski('#skF_3'),A_31)
      | ~ v1_tdlat_3(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(A_31)
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_369])).

tff(c_544,plain,(
    ! [A_31] :
      ( v2_tex_2(k1_tarski('#skF_3'),A_31)
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(A_31)
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_497])).

tff(c_563,plain,(
    ! [A_129] :
      ( v2_tex_2(k1_tarski('#skF_3'),A_129)
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_544])).

tff(c_56,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_175,plain,(
    ~ v2_tex_2(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_56])).

tff(c_566,plain,
    ( v2_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_563,c_175])).

tff(c_569,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_282,c_566])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_569])).

tff(c_573,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_581,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_573,c_20])).

tff(c_584,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_581])).

tff(c_587,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_584])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:05:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  %$ v2_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.76/1.41  
% 2.76/1.41  %Foreground sorts:
% 2.76/1.41  
% 2.76/1.41  
% 2.76/1.41  %Background operators:
% 2.76/1.41  
% 2.76/1.41  
% 2.76/1.41  %Foreground operators:
% 2.76/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.76/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.41  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.76/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.41  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.76/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.76/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.76/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.41  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.76/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.76/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.41  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.76/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.76/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.76/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.41  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.76/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.41  
% 2.76/1.42  tff(f_196, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.76/1.42  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.76/1.42  tff(f_142, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.76/1.42  tff(f_156, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.76/1.42  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.76/1.42  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc25_tex_2)).
% 2.76/1.42  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.76/1.42  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.76/1.42  tff(f_121, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.76/1.42  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l17_tex_2)).
% 2.76/1.42  tff(f_183, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.76/1.42  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.76/1.42  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.76/1.42  tff(c_18, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.76/1.42  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.76/1.42  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.76/1.42  tff(c_272, plain, (![A_88, B_89]: (m1_pre_topc(k1_tex_2(A_88, B_89), A_88) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.76/1.42  tff(c_277, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_272])).
% 2.76/1.42  tff(c_281, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_277])).
% 2.76/1.42  tff(c_282, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_281])).
% 2.76/1.42  tff(c_257, plain, (![A_84, B_85]: (~v2_struct_0(k1_tex_2(A_84, B_85)) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.76/1.42  tff(c_264, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_257])).
% 2.76/1.42  tff(c_268, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_264])).
% 2.76/1.42  tff(c_269, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_268])).
% 2.76/1.42  tff(c_231, plain, (![A_80, B_81]: (v7_struct_0(k1_tex_2(A_80, B_81)) | ~m1_subset_1(B_81, u1_struct_0(A_80)) | ~l1_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.76/1.42  tff(c_238, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_231])).
% 2.76/1.42  tff(c_242, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_238])).
% 2.76/1.42  tff(c_243, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_242])).
% 2.76/1.42  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.76/1.42  tff(c_16, plain, (![B_10, A_8]: (v2_pre_topc(B_10) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.42  tff(c_285, plain, (v2_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_282, c_16])).
% 2.76/1.42  tff(c_288, plain, (v2_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_285])).
% 2.76/1.42  tff(c_330, plain, (![B_103, A_104]: (v1_tdlat_3(B_103) | ~v2_pre_topc(B_103) | ~v7_struct_0(B_103) | v2_struct_0(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.76/1.42  tff(c_333, plain, (v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3')) | ~v2_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_282, c_330])).
% 2.76/1.42  tff(c_336, plain, (v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_243, c_288, c_333])).
% 2.76/1.42  tff(c_337, plain, (v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_269, c_336])).
% 2.76/1.42  tff(c_244, plain, (![A_82, B_83]: (v1_pre_topc(k1_tex_2(A_82, B_83)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.76/1.42  tff(c_251, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_244])).
% 2.76/1.42  tff(c_255, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_251])).
% 2.76/1.42  tff(c_256, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_255])).
% 2.76/1.42  tff(c_69, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.42  tff(c_77, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_69])).
% 2.76/1.42  tff(c_78, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.76/1.42  tff(c_154, plain, (![A_69, B_70]: (k6_domain_1(A_69, B_70)=k1_tarski(B_70) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.42  tff(c_163, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_154])).
% 2.76/1.42  tff(c_168, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_163])).
% 2.76/1.42  tff(c_470, plain, (![A_127, B_128]: (k6_domain_1(u1_struct_0(A_127), B_128)=u1_struct_0(k1_tex_2(A_127, B_128)) | ~m1_pre_topc(k1_tex_2(A_127, B_128), A_127) | ~v1_pre_topc(k1_tex_2(A_127, B_128)) | v2_struct_0(k1_tex_2(A_127, B_128)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.76/1.42  tff(c_474, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_282, c_470])).
% 2.76/1.42  tff(c_478, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=k1_tarski('#skF_3') | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_256, c_168, c_474])).
% 2.76/1.42  tff(c_479, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_269, c_478])).
% 2.76/1.42  tff(c_50, plain, (![B_33, A_31]: (m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.76/1.42  tff(c_358, plain, (![B_109, A_110]: (v2_tex_2(u1_struct_0(B_109), A_110) | ~v1_tdlat_3(B_109) | ~m1_subset_1(u1_struct_0(B_109), k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_pre_topc(B_109, A_110) | v2_struct_0(B_109) | ~l1_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_183])).
% 2.76/1.42  tff(c_369, plain, (![B_33, A_31]: (v2_tex_2(u1_struct_0(B_33), A_31) | ~v1_tdlat_3(B_33) | v2_struct_0(B_33) | v2_struct_0(A_31) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_50, c_358])).
% 2.76/1.42  tff(c_497, plain, (![A_31]: (v2_tex_2(k1_tarski('#skF_3'), A_31) | ~v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(A_31) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_31) | ~l1_pre_topc(A_31))), inference(superposition, [status(thm), theory('equality')], [c_479, c_369])).
% 2.76/1.42  tff(c_544, plain, (![A_31]: (v2_tex_2(k1_tarski('#skF_3'), A_31) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(A_31) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_31) | ~l1_pre_topc(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_497])).
% 2.76/1.42  tff(c_563, plain, (![A_129]: (v2_tex_2(k1_tarski('#skF_3'), A_129) | v2_struct_0(A_129) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_129) | ~l1_pre_topc(A_129))), inference(negUnitSimplification, [status(thm)], [c_269, c_544])).
% 2.76/1.42  tff(c_56, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.76/1.42  tff(c_175, plain, (~v2_tex_2(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_56])).
% 2.76/1.42  tff(c_566, plain, (v2_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_563, c_175])).
% 2.76/1.42  tff(c_569, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_282, c_566])).
% 2.76/1.42  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_569])).
% 2.76/1.42  tff(c_573, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_77])).
% 2.76/1.42  tff(c_20, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.42  tff(c_581, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_573, c_20])).
% 2.76/1.42  tff(c_584, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_581])).
% 2.76/1.42  tff(c_587, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_584])).
% 2.76/1.42  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_587])).
% 2.76/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  Inference rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Ref     : 0
% 2.76/1.42  #Sup     : 103
% 2.76/1.42  #Fact    : 0
% 2.76/1.42  #Define  : 0
% 2.76/1.42  #Split   : 2
% 2.76/1.42  #Chain   : 0
% 2.76/1.42  #Close   : 0
% 2.76/1.42  
% 2.76/1.42  Ordering : KBO
% 2.76/1.42  
% 2.76/1.42  Simplification rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Subsume      : 10
% 2.76/1.42  #Demod        : 39
% 2.76/1.42  #Tautology    : 42
% 2.76/1.42  #SimpNegUnit  : 26
% 2.76/1.42  #BackRed      : 5
% 2.76/1.42  
% 2.76/1.42  #Partial instantiations: 0
% 2.76/1.42  #Strategies tried      : 1
% 2.76/1.42  
% 2.76/1.42  Timing (in seconds)
% 2.76/1.42  ----------------------
% 2.76/1.43  Preprocessing        : 0.34
% 2.76/1.43  Parsing              : 0.18
% 2.76/1.43  CNF conversion       : 0.02
% 2.76/1.43  Main loop            : 0.30
% 2.76/1.43  Inferencing          : 0.11
% 2.76/1.43  Reduction            : 0.09
% 2.76/1.43  Demodulation         : 0.05
% 2.76/1.43  BG Simplification    : 0.02
% 2.76/1.43  Subsumption          : 0.05
% 2.76/1.43  Abstraction          : 0.02
% 2.76/1.43  MUC search           : 0.00
% 2.76/1.43  Cooper               : 0.00
% 2.76/1.43  Total                : 0.67
% 2.76/1.43  Index Insertion      : 0.00
% 2.76/1.43  Index Deletion       : 0.00
% 2.76/1.43  Index Matching       : 0.00
% 2.76/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
