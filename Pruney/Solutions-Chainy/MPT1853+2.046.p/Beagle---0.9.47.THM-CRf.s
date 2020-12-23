%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:06 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 666 expanded)
%              Number of leaves         :   39 ( 226 expanded)
%              Depth                    :   12
%              Number of atoms          :  309 (1763 expanded)
%              Number of equality atoms :   48 ( 294 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_127,axiom,(
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

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_66,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1020,plain,(
    ! [A_189,B_190] :
      ( k6_domain_1(A_189,B_190) = k1_tarski(B_190)
      | ~ m1_subset_1(B_190,A_189)
      | v1_xboole_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1032,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_1020])).

tff(c_1052,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1032])).

tff(c_30,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1055,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1052,c_30])).

tff(c_1058,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1055])).

tff(c_1062,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1058])).

tff(c_1066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1062])).

tff(c_1068,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1032])).

tff(c_1067,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1032])).

tff(c_1078,plain,(
    ! [A_197,B_198] :
      ( v1_zfmisc_1(A_197)
      | k6_domain_1(A_197,B_198) != A_197
      | ~ m1_subset_1(B_198,A_197)
      | v1_xboole_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1087,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_1078])).

tff(c_1091,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') != k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_1087])).

tff(c_1092,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') != k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1091])).

tff(c_1093,plain,(
    u1_struct_0('#skF_5') != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1092])).

tff(c_70,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_105,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_386,plain,(
    ! [A_110,B_111] :
      ( m1_pre_topc(k1_tex_2(A_110,B_111),A_110)
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_391,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_386])).

tff(c_395,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_391])).

tff(c_396,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_395])).

tff(c_158,plain,(
    ! [A_79,B_80] :
      ( k6_domain_1(A_79,B_80) = k1_tarski(B_80)
      | ~ m1_subset_1(B_80,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_170,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_158])).

tff(c_181,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_184,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_30])).

tff(c_187,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_184])).

tff(c_190,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_190])).

tff(c_195,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_76,plain,
    ( v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_138,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_76])).

tff(c_201,plain,(
    v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_138])).

tff(c_320,plain,(
    ! [A_103,B_104] :
      ( ~ v2_struct_0(k1_tex_2(A_103,B_104))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_327,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_320])).

tff(c_331,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_327])).

tff(c_332,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_331])).

tff(c_255,plain,(
    ! [A_93,B_94] :
      ( v1_pre_topc(k1_tex_2(A_93,B_94))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_262,plain,
    ( v1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_255])).

tff(c_266,plain,
    ( v1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_262])).

tff(c_267,plain,(
    v1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_266])).

tff(c_397,plain,(
    ! [B_112,A_113] :
      ( u1_struct_0(B_112) = '#skF_4'(A_113,B_112)
      | v1_tex_2(B_112,A_113)
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_403,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_397,c_105])).

tff(c_407,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_403])).

tff(c_436,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_407])).

tff(c_930,plain,(
    ! [A_173,B_174] :
      ( k6_domain_1(u1_struct_0(A_173),B_174) = u1_struct_0(k1_tex_2(A_173,B_174))
      | ~ m1_pre_topc(k1_tex_2(A_173,B_174),A_173)
      | ~ v1_pre_topc(k1_tex_2(A_173,B_174))
      | v2_struct_0(k1_tex_2(A_173,B_174))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_936,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = u1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_930])).

tff(c_944,plain,
    ( '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6')
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_267,c_195,c_436,c_936])).

tff(c_945,plain,(
    '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_332,c_944])).

tff(c_42,plain,(
    ! [A_26,B_32] :
      ( ~ v1_subset_1('#skF_4'(A_26,B_32),u1_struct_0(A_26))
      | v1_tex_2(B_32,A_26)
      | ~ m1_pre_topc(B_32,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_963,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_42])).

tff(c_973,plain,(
    v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_396,c_201,c_963])).

tff(c_975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_973])).

tff(c_976,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1073,plain,(
    ~ v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_976])).

tff(c_1178,plain,(
    ! [A_215,B_216] :
      ( v1_subset_1(k6_domain_1(A_215,B_216),A_215)
      | ~ m1_subset_1(B_216,A_215)
      | v1_zfmisc_1(A_215)
      | v1_xboole_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1187,plain,
    ( v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_1178])).

tff(c_1196,plain,
    ( v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1187])).

tff(c_1197,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1073,c_1196])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_3'(A_22),A_22)
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1095,plain,(
    ! [A_201] :
      ( k6_domain_1(A_201,'#skF_3'(A_201)) = k1_tarski('#skF_3'(A_201))
      | ~ v1_zfmisc_1(A_201)
      | v1_xboole_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_38,c_1020])).

tff(c_36,plain,(
    ! [A_22] :
      ( k6_domain_1(A_22,'#skF_3'(A_22)) = A_22
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1299,plain,(
    ! [A_231] :
      ( k1_tarski('#skF_3'(A_231)) = A_231
      | ~ v1_zfmisc_1(A_231)
      | v1_xboole_0(A_231)
      | ~ v1_zfmisc_1(A_231)
      | v1_xboole_0(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_36])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1450,plain,(
    ! [C_254,A_255] :
      ( C_254 = '#skF_3'(A_255)
      | ~ r2_hidden(C_254,A_255)
      | ~ v1_zfmisc_1(A_255)
      | v1_xboole_0(A_255)
      | ~ v1_zfmisc_1(A_255)
      | v1_xboole_0(A_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_2])).

tff(c_1473,plain,(
    ! [A_256,B_257] :
      ( A_256 = '#skF_3'(B_257)
      | ~ v1_zfmisc_1(B_257)
      | v1_xboole_0(B_257)
      | ~ m1_subset_1(A_256,B_257) ) ),
    inference(resolution,[status(thm)],[c_20,c_1450])).

tff(c_1485,plain,
    ( '#skF_3'(u1_struct_0('#skF_5')) = '#skF_6'
    | ~ v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_1473])).

tff(c_1492,plain,
    ( '#skF_3'(u1_struct_0('#skF_5')) = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1485])).

tff(c_1493,plain,(
    '#skF_3'(u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1492])).

tff(c_1101,plain,(
    ! [A_201] :
      ( k1_tarski('#skF_3'(A_201)) = A_201
      | ~ v1_zfmisc_1(A_201)
      | v1_xboole_0(A_201)
      | ~ v1_zfmisc_1(A_201)
      | v1_xboole_0(A_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_36])).

tff(c_1500,plain,
    ( u1_struct_0('#skF_5') = k1_tarski('#skF_6')
    | ~ v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1493,c_1101])).

tff(c_1516,plain,
    ( u1_struct_0('#skF_5') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1197,c_1500])).

tff(c_1518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1093,c_1516])).

tff(c_1520,plain,(
    u1_struct_0('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_1525,plain,(
    m1_subset_1('#skF_6',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_64])).

tff(c_1582,plain,(
    ! [A_260,B_261] :
      ( ~ v2_struct_0(k1_tex_2(A_260,B_261))
      | ~ m1_subset_1(B_261,u1_struct_0(A_260))
      | ~ l1_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1585,plain,(
    ! [B_261] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_261))
      | ~ m1_subset_1(B_261,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_1582])).

tff(c_1591,plain,(
    ! [B_261] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_261))
      | ~ m1_subset_1(B_261,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1585])).

tff(c_1594,plain,(
    ! [B_262] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_262))
      | ~ m1_subset_1(B_262,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1591])).

tff(c_1602,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1525,c_1594])).

tff(c_977,plain,(
    v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1723,plain,(
    ! [B_279,A_280] :
      ( ~ v1_tex_2(B_279,A_280)
      | u1_struct_0(B_279) != u1_struct_0(A_280)
      | ~ m1_pre_topc(B_279,A_280)
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1726,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) != u1_struct_0('#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_977,c_1723])).

tff(c_1729,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) != k1_tarski('#skF_6')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1520,c_1726])).

tff(c_1730,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1729])).

tff(c_1802,plain,(
    ! [A_288,B_289] :
      ( m1_pre_topc(k1_tex_2(A_288,B_289),A_288)
      | ~ m1_subset_1(B_289,u1_struct_0(A_288))
      | ~ l1_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1804,plain,(
    ! [B_289] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_289),'#skF_5')
      | ~ m1_subset_1(B_289,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_1802])).

tff(c_1809,plain,(
    ! [B_289] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_289),'#skF_5')
      | ~ m1_subset_1(B_289,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1804])).

tff(c_1818,plain,(
    ! [B_292] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_292),'#skF_5')
      | ~ m1_subset_1(B_292,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1809])).

tff(c_1821,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1525,c_1818])).

tff(c_1829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1730,c_1821])).

tff(c_1830,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) != k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_1628,plain,(
    ! [A_264,B_265] :
      ( v1_pre_topc(k1_tex_2(A_264,B_265))
      | ~ m1_subset_1(B_265,u1_struct_0(A_264))
      | ~ l1_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1631,plain,(
    ! [B_265] :
      ( v1_pre_topc(k1_tex_2('#skF_5',B_265))
      | ~ m1_subset_1(B_265,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_1628])).

tff(c_1637,plain,(
    ! [B_265] :
      ( v1_pre_topc(k1_tex_2('#skF_5',B_265))
      | ~ m1_subset_1(B_265,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1631])).

tff(c_1658,plain,(
    ! [B_268] :
      ( v1_pre_topc(k1_tex_2('#skF_5',B_268))
      | ~ m1_subset_1(B_268,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1637])).

tff(c_1666,plain,(
    v1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1525,c_1658])).

tff(c_1523,plain,(
    k6_domain_1(k1_tarski('#skF_6'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_1067])).

tff(c_1831,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_2375,plain,(
    ! [A_351,B_352] :
      ( k6_domain_1(u1_struct_0(A_351),B_352) = u1_struct_0(k1_tex_2(A_351,B_352))
      | ~ m1_pre_topc(k1_tex_2(A_351,B_352),A_351)
      | ~ v1_pre_topc(k1_tex_2(A_351,B_352))
      | v2_struct_0(k1_tex_2(A_351,B_352))
      | ~ m1_subset_1(B_352,u1_struct_0(A_351))
      | ~ l1_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2377,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = u1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1831,c_2375])).

tff(c_2380,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6')
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1525,c_1520,c_1666,c_1523,c_1520,c_2377])).

tff(c_2382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1602,c_1830,c_2380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.91  
% 4.57/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.91  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 4.57/1.91  
% 4.57/1.91  %Foreground sorts:
% 4.57/1.91  
% 4.57/1.91  
% 4.57/1.91  %Background operators:
% 4.57/1.91  
% 4.57/1.91  
% 4.57/1.91  %Foreground operators:
% 4.57/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.57/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.91  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.57/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.57/1.91  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 4.57/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.57/1.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.57/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.57/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.57/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.57/1.91  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.57/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.57/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.91  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 4.57/1.91  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.57/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.57/1.91  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.57/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.57/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.57/1.91  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.57/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.57/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.91  
% 4.57/1.93  tff(f_186, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 4.57/1.93  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.57/1.93  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.57/1.93  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.57/1.93  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 4.57/1.93  tff(f_141, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 4.57/1.93  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 4.57/1.93  tff(f_127, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 4.57/1.93  tff(f_173, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 4.57/1.93  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.57/1.93  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.57/1.93  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 4.57/1.93  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.57/1.93  tff(c_66, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.57/1.93  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.93  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.57/1.93  tff(c_1020, plain, (![A_189, B_190]: (k6_domain_1(A_189, B_190)=k1_tarski(B_190) | ~m1_subset_1(B_190, A_189) | v1_xboole_0(A_189))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.57/1.93  tff(c_1032, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1020])).
% 4.57/1.93  tff(c_1052, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1032])).
% 4.57/1.93  tff(c_30, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.57/1.93  tff(c_1055, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1052, c_30])).
% 4.57/1.93  tff(c_1058, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_1055])).
% 4.57/1.93  tff(c_1062, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1058])).
% 4.57/1.93  tff(c_1066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1062])).
% 4.57/1.93  tff(c_1068, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1032])).
% 4.57/1.93  tff(c_1067, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1032])).
% 4.57/1.93  tff(c_1078, plain, (![A_197, B_198]: (v1_zfmisc_1(A_197) | k6_domain_1(A_197, B_198)!=A_197 | ~m1_subset_1(B_198, A_197) | v1_xboole_0(A_197))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.57/1.93  tff(c_1087, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')!=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1078])).
% 4.57/1.93  tff(c_1091, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')!=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_1087])).
% 4.57/1.93  tff(c_1092, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')!=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1068, c_1091])).
% 4.57/1.93  tff(c_1093, plain, (u1_struct_0('#skF_5')!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_1092])).
% 4.57/1.93  tff(c_70, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.57/1.93  tff(c_105, plain, (~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 4.57/1.93  tff(c_386, plain, (![A_110, B_111]: (m1_pre_topc(k1_tex_2(A_110, B_111), A_110) | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.57/1.93  tff(c_391, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_386])).
% 4.57/1.93  tff(c_395, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_391])).
% 4.57/1.93  tff(c_396, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_395])).
% 4.57/1.93  tff(c_158, plain, (![A_79, B_80]: (k6_domain_1(A_79, B_80)=k1_tarski(B_80) | ~m1_subset_1(B_80, A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.57/1.93  tff(c_170, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_158])).
% 4.57/1.93  tff(c_181, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_170])).
% 4.57/1.93  tff(c_184, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_181, c_30])).
% 4.57/1.93  tff(c_187, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_184])).
% 4.57/1.93  tff(c_190, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_187])).
% 4.57/1.93  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_190])).
% 4.57/1.93  tff(c_195, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_170])).
% 4.57/1.93  tff(c_76, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.57/1.93  tff(c_138, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_105, c_76])).
% 4.57/1.93  tff(c_201, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_138])).
% 4.57/1.93  tff(c_320, plain, (![A_103, B_104]: (~v2_struct_0(k1_tex_2(A_103, B_104)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.57/1.93  tff(c_327, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_320])).
% 4.57/1.93  tff(c_331, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_327])).
% 4.57/1.93  tff(c_332, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_331])).
% 4.57/1.93  tff(c_255, plain, (![A_93, B_94]: (v1_pre_topc(k1_tex_2(A_93, B_94)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.57/1.93  tff(c_262, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_255])).
% 4.57/1.93  tff(c_266, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_262])).
% 4.57/1.93  tff(c_267, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_266])).
% 4.57/1.93  tff(c_397, plain, (![B_112, A_113]: (u1_struct_0(B_112)='#skF_4'(A_113, B_112) | v1_tex_2(B_112, A_113) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.57/1.93  tff(c_403, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_397, c_105])).
% 4.57/1.93  tff(c_407, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_403])).
% 4.57/1.93  tff(c_436, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_407])).
% 4.57/1.93  tff(c_930, plain, (![A_173, B_174]: (k6_domain_1(u1_struct_0(A_173), B_174)=u1_struct_0(k1_tex_2(A_173, B_174)) | ~m1_pre_topc(k1_tex_2(A_173, B_174), A_173) | ~v1_pre_topc(k1_tex_2(A_173, B_174)) | v2_struct_0(k1_tex_2(A_173, B_174)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.57/1.93  tff(c_936, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=u1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_396, c_930])).
% 4.57/1.93  tff(c_944, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6') | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_267, c_195, c_436, c_936])).
% 4.57/1.93  tff(c_945, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_332, c_944])).
% 4.57/1.93  tff(c_42, plain, (![A_26, B_32]: (~v1_subset_1('#skF_4'(A_26, B_32), u1_struct_0(A_26)) | v1_tex_2(B_32, A_26) | ~m1_pre_topc(B_32, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.57/1.93  tff(c_963, plain, (~v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_945, c_42])).
% 4.57/1.93  tff(c_973, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_396, c_201, c_963])).
% 4.57/1.93  tff(c_975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_973])).
% 4.57/1.93  tff(c_976, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_70])).
% 4.57/1.93  tff(c_1073, plain, (~v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_976])).
% 4.57/1.93  tff(c_1178, plain, (![A_215, B_216]: (v1_subset_1(k6_domain_1(A_215, B_216), A_215) | ~m1_subset_1(B_216, A_215) | v1_zfmisc_1(A_215) | v1_xboole_0(A_215))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.57/1.93  tff(c_1187, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_1178])).
% 4.57/1.93  tff(c_1196, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1187])).
% 4.57/1.93  tff(c_1197, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1068, c_1073, c_1196])).
% 4.57/1.93  tff(c_20, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.57/1.93  tff(c_38, plain, (![A_22]: (m1_subset_1('#skF_3'(A_22), A_22) | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.57/1.93  tff(c_1095, plain, (![A_201]: (k6_domain_1(A_201, '#skF_3'(A_201))=k1_tarski('#skF_3'(A_201)) | ~v1_zfmisc_1(A_201) | v1_xboole_0(A_201))), inference(resolution, [status(thm)], [c_38, c_1020])).
% 4.57/1.93  tff(c_36, plain, (![A_22]: (k6_domain_1(A_22, '#skF_3'(A_22))=A_22 | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.57/1.93  tff(c_1299, plain, (![A_231]: (k1_tarski('#skF_3'(A_231))=A_231 | ~v1_zfmisc_1(A_231) | v1_xboole_0(A_231) | ~v1_zfmisc_1(A_231) | v1_xboole_0(A_231))), inference(superposition, [status(thm), theory('equality')], [c_1095, c_36])).
% 4.57/1.93  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.57/1.93  tff(c_1450, plain, (![C_254, A_255]: (C_254='#skF_3'(A_255) | ~r2_hidden(C_254, A_255) | ~v1_zfmisc_1(A_255) | v1_xboole_0(A_255) | ~v1_zfmisc_1(A_255) | v1_xboole_0(A_255))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_2])).
% 4.57/1.93  tff(c_1473, plain, (![A_256, B_257]: (A_256='#skF_3'(B_257) | ~v1_zfmisc_1(B_257) | v1_xboole_0(B_257) | ~m1_subset_1(A_256, B_257))), inference(resolution, [status(thm)], [c_20, c_1450])).
% 4.57/1.93  tff(c_1485, plain, ('#skF_3'(u1_struct_0('#skF_5'))='#skF_6' | ~v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1473])).
% 4.57/1.93  tff(c_1492, plain, ('#skF_3'(u1_struct_0('#skF_5'))='#skF_6' | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1485])).
% 4.57/1.93  tff(c_1493, plain, ('#skF_3'(u1_struct_0('#skF_5'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1068, c_1492])).
% 4.57/1.93  tff(c_1101, plain, (![A_201]: (k1_tarski('#skF_3'(A_201))=A_201 | ~v1_zfmisc_1(A_201) | v1_xboole_0(A_201) | ~v1_zfmisc_1(A_201) | v1_xboole_0(A_201))), inference(superposition, [status(thm), theory('equality')], [c_1095, c_36])).
% 4.57/1.93  tff(c_1500, plain, (u1_struct_0('#skF_5')=k1_tarski('#skF_6') | ~v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1493, c_1101])).
% 4.57/1.93  tff(c_1516, plain, (u1_struct_0('#skF_5')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1197, c_1500])).
% 4.57/1.93  tff(c_1518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1068, c_1093, c_1516])).
% 4.57/1.93  tff(c_1520, plain, (u1_struct_0('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1092])).
% 4.57/1.93  tff(c_1525, plain, (m1_subset_1('#skF_6', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_64])).
% 4.57/1.93  tff(c_1582, plain, (![A_260, B_261]: (~v2_struct_0(k1_tex_2(A_260, B_261)) | ~m1_subset_1(B_261, u1_struct_0(A_260)) | ~l1_pre_topc(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.57/1.93  tff(c_1585, plain, (![B_261]: (~v2_struct_0(k1_tex_2('#skF_5', B_261)) | ~m1_subset_1(B_261, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1520, c_1582])).
% 4.57/1.93  tff(c_1591, plain, (![B_261]: (~v2_struct_0(k1_tex_2('#skF_5', B_261)) | ~m1_subset_1(B_261, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1585])).
% 4.57/1.93  tff(c_1594, plain, (![B_262]: (~v2_struct_0(k1_tex_2('#skF_5', B_262)) | ~m1_subset_1(B_262, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1591])).
% 4.57/1.93  tff(c_1602, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1525, c_1594])).
% 4.57/1.93  tff(c_977, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 4.57/1.93  tff(c_1723, plain, (![B_279, A_280]: (~v1_tex_2(B_279, A_280) | u1_struct_0(B_279)!=u1_struct_0(A_280) | ~m1_pre_topc(B_279, A_280) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.57/1.93  tff(c_1726, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))!=u1_struct_0('#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_977, c_1723])).
% 4.57/1.93  tff(c_1729, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))!=k1_tarski('#skF_6') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1520, c_1726])).
% 4.57/1.93  tff(c_1730, plain, (~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1729])).
% 4.57/1.93  tff(c_1802, plain, (![A_288, B_289]: (m1_pre_topc(k1_tex_2(A_288, B_289), A_288) | ~m1_subset_1(B_289, u1_struct_0(A_288)) | ~l1_pre_topc(A_288) | v2_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.57/1.93  tff(c_1804, plain, (![B_289]: (m1_pre_topc(k1_tex_2('#skF_5', B_289), '#skF_5') | ~m1_subset_1(B_289, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1520, c_1802])).
% 4.57/1.93  tff(c_1809, plain, (![B_289]: (m1_pre_topc(k1_tex_2('#skF_5', B_289), '#skF_5') | ~m1_subset_1(B_289, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1804])).
% 4.57/1.93  tff(c_1818, plain, (![B_292]: (m1_pre_topc(k1_tex_2('#skF_5', B_292), '#skF_5') | ~m1_subset_1(B_292, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1809])).
% 4.57/1.93  tff(c_1821, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_1525, c_1818])).
% 4.57/1.93  tff(c_1829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1730, c_1821])).
% 4.57/1.93  tff(c_1830, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))!=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1729])).
% 4.57/1.93  tff(c_1628, plain, (![A_264, B_265]: (v1_pre_topc(k1_tex_2(A_264, B_265)) | ~m1_subset_1(B_265, u1_struct_0(A_264)) | ~l1_pre_topc(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.57/1.93  tff(c_1631, plain, (![B_265]: (v1_pre_topc(k1_tex_2('#skF_5', B_265)) | ~m1_subset_1(B_265, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1520, c_1628])).
% 4.57/1.93  tff(c_1637, plain, (![B_265]: (v1_pre_topc(k1_tex_2('#skF_5', B_265)) | ~m1_subset_1(B_265, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1631])).
% 4.57/1.93  tff(c_1658, plain, (![B_268]: (v1_pre_topc(k1_tex_2('#skF_5', B_268)) | ~m1_subset_1(B_268, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1637])).
% 4.57/1.93  tff(c_1666, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1525, c_1658])).
% 4.57/1.93  tff(c_1523, plain, (k6_domain_1(k1_tarski('#skF_6'), '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_1067])).
% 4.57/1.93  tff(c_1831, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_1729])).
% 4.57/1.93  tff(c_2375, plain, (![A_351, B_352]: (k6_domain_1(u1_struct_0(A_351), B_352)=u1_struct_0(k1_tex_2(A_351, B_352)) | ~m1_pre_topc(k1_tex_2(A_351, B_352), A_351) | ~v1_pre_topc(k1_tex_2(A_351, B_352)) | v2_struct_0(k1_tex_2(A_351, B_352)) | ~m1_subset_1(B_352, u1_struct_0(A_351)) | ~l1_pre_topc(A_351) | v2_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.57/1.93  tff(c_2377, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=u1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1831, c_2375])).
% 4.57/1.93  tff(c_2380, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6') | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1525, c_1520, c_1666, c_1523, c_1520, c_2377])).
% 4.57/1.93  tff(c_2382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1602, c_1830, c_2380])).
% 4.57/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.93  
% 4.57/1.93  Inference rules
% 4.57/1.93  ----------------------
% 4.57/1.93  #Ref     : 0
% 4.57/1.93  #Sup     : 477
% 4.57/1.93  #Fact    : 0
% 4.57/1.93  #Define  : 0
% 4.57/1.93  #Split   : 11
% 4.57/1.93  #Chain   : 0
% 4.57/1.93  #Close   : 0
% 4.57/1.93  
% 4.57/1.93  Ordering : KBO
% 4.57/1.93  
% 4.57/1.93  Simplification rules
% 4.57/1.93  ----------------------
% 4.57/1.93  #Subsume      : 73
% 4.57/1.93  #Demod        : 218
% 4.57/1.93  #Tautology    : 154
% 4.57/1.93  #SimpNegUnit  : 106
% 4.57/1.93  #BackRed      : 15
% 4.57/1.93  
% 4.57/1.93  #Partial instantiations: 0
% 4.57/1.93  #Strategies tried      : 1
% 4.57/1.93  
% 4.57/1.93  Timing (in seconds)
% 4.57/1.93  ----------------------
% 4.57/1.93  Preprocessing        : 0.40
% 4.57/1.93  Parsing              : 0.21
% 4.57/1.93  CNF conversion       : 0.03
% 4.57/1.93  Main loop            : 0.73
% 4.57/1.93  Inferencing          : 0.27
% 4.57/1.93  Reduction            : 0.22
% 4.57/1.93  Demodulation         : 0.14
% 4.57/1.93  BG Simplification    : 0.04
% 4.57/1.93  Subsumption          : 0.15
% 4.57/1.93  Abstraction          : 0.04
% 4.57/1.93  MUC search           : 0.00
% 4.57/1.93  Cooper               : 0.00
% 4.57/1.93  Total                : 1.18
% 4.57/1.93  Index Insertion      : 0.00
% 4.57/1.93  Index Deletion       : 0.00
% 4.57/1.93  Index Matching       : 0.00
% 4.57/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
