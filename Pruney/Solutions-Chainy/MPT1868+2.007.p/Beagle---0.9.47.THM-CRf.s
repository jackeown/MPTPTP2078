%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:36 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  121 (1197 expanded)
%              Number of leaves         :   39 ( 410 expanded)
%              Depth                    :   19
%              Number of atoms          :  297 (3272 expanded)
%              Number of equality atoms :   39 ( 435 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_187,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_119,axiom,(
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

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v2_pre_topc(k1_tex_2(A,B))
           => ( v1_tdlat_3(k1_tex_2(A,B))
              & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_174,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_119,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_119])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_30,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_133,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_30])).

tff(c_136,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_133])).

tff(c_139,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_139])).

tff(c_144,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_56,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_158,plain,(
    ~ v2_tex_2(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_56])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tarski(A_7),k1_zfmisc_1(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [B_69,A_70,A_71] :
      ( ~ v1_xboole_0(B_69)
      | ~ r2_hidden(A_70,k1_tarski(A_71))
      | ~ r2_hidden(A_71,B_69) ) ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_109,plain,(
    ! [B_72,C_73] :
      ( ~ v1_xboole_0(B_72)
      | ~ r2_hidden(C_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_117,plain,(
    ! [C_5] : ~ v1_xboole_0(k1_tarski(C_5)) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_145,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k6_domain_1(A_23,B_24),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_162,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_32])).

tff(c_166,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_162])).

tff(c_167,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_166])).

tff(c_318,plain,(
    ! [A_103,B_104] :
      ( ~ v2_struct_0('#skF_3'(A_103,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_xboole_0(B_104)
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_321,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_318])).

tff(c_332,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_321])).

tff(c_333,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_117,c_332])).

tff(c_298,plain,(
    ! [A_101,B_102] :
      ( v1_pre_topc('#skF_3'(A_101,B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(B_102)
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_301,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_298])).

tff(c_312,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_301])).

tff(c_313,plain,(
    v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_117,c_312])).

tff(c_349,plain,(
    ! [A_110,B_111] :
      ( u1_struct_0('#skF_3'(A_110,B_111)) = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | v1_xboole_0(B_111)
      | ~ l1_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_352,plain,
    ( u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_349])).

tff(c_363,plain,
    ( u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_352])).

tff(c_364,plain,(
    u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_117,c_363])).

tff(c_827,plain,(
    ! [A_158,B_159] :
      ( m1_pre_topc('#skF_3'(A_158,B_159),A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_xboole_0(B_159)
      | ~ l1_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_833,plain,
    ( m1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_827])).

tff(c_843,plain,
    ( m1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_833])).

tff(c_844,plain,(
    m1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_117,c_843])).

tff(c_1092,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_tex_2(A_191,B_192) = C_193
      | u1_struct_0(C_193) != k6_domain_1(u1_struct_0(A_191),B_192)
      | ~ m1_pre_topc(C_193,A_191)
      | ~ v1_pre_topc(C_193)
      | v2_struct_0(C_193)
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1106,plain,(
    ! [C_193] :
      ( k1_tex_2('#skF_4','#skF_5') = C_193
      | u1_struct_0(C_193) != k1_tarski('#skF_5')
      | ~ m1_pre_topc(C_193,'#skF_4')
      | ~ v1_pre_topc(C_193)
      | v2_struct_0(C_193)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1092])).

tff(c_1114,plain,(
    ! [C_193] :
      ( k1_tex_2('#skF_4','#skF_5') = C_193
      | u1_struct_0(C_193) != k1_tarski('#skF_5')
      | ~ m1_pre_topc(C_193,'#skF_4')
      | ~ v1_pre_topc(C_193)
      | v2_struct_0(C_193)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1106])).

tff(c_1116,plain,(
    ! [C_194] :
      ( k1_tex_2('#skF_4','#skF_5') = C_194
      | u1_struct_0(C_194) != k1_tarski('#skF_5')
      | ~ m1_pre_topc(C_194,'#skF_4')
      | ~ v1_pre_topc(C_194)
      | v2_struct_0(C_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1114])).

tff(c_1123,plain,
    ( '#skF_3'('#skF_4',k1_tarski('#skF_5')) = k1_tex_2('#skF_4','#skF_5')
    | u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) != k1_tarski('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_844,c_1116])).

tff(c_1130,plain,
    ( '#skF_3'('#skF_4',k1_tarski('#skF_5')) = k1_tex_2('#skF_4','#skF_5')
    | v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_364,c_1123])).

tff(c_1131,plain,(
    '#skF_3'('#skF_4',k1_tarski('#skF_5')) = k1_tex_2('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_1130])).

tff(c_1141,plain,(
    m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_844])).

tff(c_1143,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_333])).

tff(c_439,plain,(
    ! [A_114,B_115] :
      ( v1_tdlat_3(k1_tex_2(A_114,B_115))
      | ~ v2_pre_topc(k1_tex_2(A_114,B_115))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_448,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_439])).

tff(c_452,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_448])).

tff(c_453,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_452])).

tff(c_454,plain,(
    ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_455,plain,(
    ! [A_116,B_117] :
      ( m1_pre_topc('#skF_3'(A_116,B_117),A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(B_117)
      | ~ l1_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_461,plain,
    ( m1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_455])).

tff(c_471,plain,
    ( m1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_461])).

tff(c_472,plain,(
    m1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_117,c_471])).

tff(c_754,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_tex_2(A_152,B_153) = C_154
      | u1_struct_0(C_154) != k6_domain_1(u1_struct_0(A_152),B_153)
      | ~ m1_pre_topc(C_154,A_152)
      | ~ v1_pre_topc(C_154)
      | v2_struct_0(C_154)
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_768,plain,(
    ! [C_154] :
      ( k1_tex_2('#skF_4','#skF_5') = C_154
      | u1_struct_0(C_154) != k1_tarski('#skF_5')
      | ~ m1_pre_topc(C_154,'#skF_4')
      | ~ v1_pre_topc(C_154)
      | v2_struct_0(C_154)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_754])).

tff(c_776,plain,(
    ! [C_154] :
      ( k1_tex_2('#skF_4','#skF_5') = C_154
      | u1_struct_0(C_154) != k1_tarski('#skF_5')
      | ~ m1_pre_topc(C_154,'#skF_4')
      | ~ v1_pre_topc(C_154)
      | v2_struct_0(C_154)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_768])).

tff(c_778,plain,(
    ! [C_155] :
      ( k1_tex_2('#skF_4','#skF_5') = C_155
      | u1_struct_0(C_155) != k1_tarski('#skF_5')
      | ~ m1_pre_topc(C_155,'#skF_4')
      | ~ v1_pre_topc(C_155)
      | v2_struct_0(C_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_776])).

tff(c_785,plain,
    ( '#skF_3'('#skF_4',k1_tarski('#skF_5')) = k1_tex_2('#skF_4','#skF_5')
    | u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) != k1_tarski('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_472,c_778])).

tff(c_792,plain,
    ( '#skF_3'('#skF_4',k1_tarski('#skF_5')) = k1_tex_2('#skF_4','#skF_5')
    | v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_364,c_785])).

tff(c_793,plain,(
    '#skF_3'('#skF_4',k1_tarski('#skF_5')) = k1_tex_2('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_792])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( v2_pre_topc(B_16)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_479,plain,
    ( v2_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_472,c_22])).

tff(c_485,plain,(
    v2_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_479])).

tff(c_803,plain,(
    v2_pre_topc(k1_tex_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_485])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_803])).

tff(c_810,plain,(
    v1_tdlat_3(k1_tex_2('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_1142,plain,(
    u1_struct_0(k1_tex_2('#skF_4','#skF_5')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_364])).

tff(c_52,plain,(
    ! [B_47,A_43] :
      ( v2_tex_2(u1_struct_0(B_47),A_43)
      | ~ v1_tdlat_3(B_47)
      | ~ m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_47,A_43)
      | v2_struct_0(B_47)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1221,plain,(
    ! [A_43] :
      ( v2_tex_2(u1_struct_0(k1_tex_2('#skF_4','#skF_5')),A_43)
      | ~ v1_tdlat_3(k1_tex_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),A_43)
      | v2_struct_0(k1_tex_2('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_52])).

tff(c_1270,plain,(
    ! [A_43] :
      ( v2_tex_2(k1_tarski('#skF_5'),A_43)
      | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),A_43)
      | v2_struct_0(k1_tex_2('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_1142,c_1221])).

tff(c_1729,plain,(
    ! [A_228] :
      ( v2_tex_2(k1_tarski('#skF_5'),A_228)
      | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),A_228)
      | ~ l1_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1143,c_1270])).

tff(c_1744,plain,
    ( v2_tex_2(k1_tarski('#skF_5'),'#skF_4')
    | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_1729])).

tff(c_1753,plain,
    ( v2_tex_2(k1_tarski('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1141,c_1744])).

tff(c_1755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_158,c_1753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.86  
% 4.47/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.87  %$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.47/1.87  
% 4.47/1.87  %Foreground sorts:
% 4.47/1.87  
% 4.47/1.87  
% 4.47/1.87  %Background operators:
% 4.47/1.87  
% 4.47/1.87  
% 4.47/1.87  %Foreground operators:
% 4.47/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.47/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.47/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.47/1.87  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.47/1.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.47/1.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.47/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.47/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.87  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.47/1.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.47/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.47/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.87  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 4.47/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.47/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.47/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.47/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.47/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.47/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.47/1.87  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.47/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.87  
% 4.47/1.88  tff(f_187, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 4.47/1.88  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.47/1.88  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.47/1.88  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.47/1.88  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.47/1.88  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.47/1.88  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.47/1.88  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.47/1.88  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 4.47/1.88  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 4.47/1.88  tff(f_154, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tex_2)).
% 4.47/1.88  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.47/1.88  tff(f_174, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 4.47/1.88  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.47/1.88  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.47/1.88  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.47/1.88  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.47/1.88  tff(c_119, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.47/1.88  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_119])).
% 4.47/1.88  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_127])).
% 4.47/1.88  tff(c_30, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.47/1.88  tff(c_133, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_30])).
% 4.47/1.88  tff(c_136, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_133])).
% 4.47/1.88  tff(c_139, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_136])).
% 4.47/1.88  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_139])).
% 4.47/1.88  tff(c_144, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_127])).
% 4.47/1.88  tff(c_56, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.47/1.88  tff(c_158, plain, (~v2_tex_2(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_56])).
% 4.47/1.88  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.88  tff(c_16, plain, (![A_7, B_8]: (m1_subset_1(k1_tarski(A_7), k1_zfmisc_1(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.47/1.88  tff(c_96, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.47/1.88  tff(c_101, plain, (![B_69, A_70, A_71]: (~v1_xboole_0(B_69) | ~r2_hidden(A_70, k1_tarski(A_71)) | ~r2_hidden(A_71, B_69))), inference(resolution, [status(thm)], [c_16, c_96])).
% 4.47/1.88  tff(c_109, plain, (![B_72, C_73]: (~v1_xboole_0(B_72) | ~r2_hidden(C_73, B_72))), inference(resolution, [status(thm)], [c_4, c_101])).
% 4.47/1.88  tff(c_117, plain, (![C_5]: (~v1_xboole_0(k1_tarski(C_5)))), inference(resolution, [status(thm)], [c_4, c_109])).
% 4.47/1.88  tff(c_145, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_127])).
% 4.47/1.88  tff(c_32, plain, (![A_23, B_24]: (m1_subset_1(k6_domain_1(A_23, B_24), k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.47/1.88  tff(c_162, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_32])).
% 4.47/1.88  tff(c_166, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_162])).
% 4.47/1.88  tff(c_167, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_145, c_166])).
% 4.47/1.88  tff(c_318, plain, (![A_103, B_104]: (~v2_struct_0('#skF_3'(A_103, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | v1_xboole_0(B_104) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.47/1.88  tff(c_321, plain, (~v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_167, c_318])).
% 4.47/1.88  tff(c_332, plain, (~v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_321])).
% 4.47/1.88  tff(c_333, plain, (~v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_117, c_332])).
% 4.47/1.88  tff(c_298, plain, (![A_101, B_102]: (v1_pre_topc('#skF_3'(A_101, B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(B_102) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.47/1.88  tff(c_301, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_167, c_298])).
% 4.47/1.88  tff(c_312, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_301])).
% 4.47/1.88  tff(c_313, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_117, c_312])).
% 4.47/1.89  tff(c_349, plain, (![A_110, B_111]: (u1_struct_0('#skF_3'(A_110, B_111))=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | v1_xboole_0(B_111) | ~l1_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.47/1.89  tff(c_352, plain, (u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | v1_xboole_0(k1_tarski('#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_167, c_349])).
% 4.47/1.89  tff(c_363, plain, (u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | v1_xboole_0(k1_tarski('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_352])).
% 4.47/1.89  tff(c_364, plain, (u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_117, c_363])).
% 4.47/1.89  tff(c_827, plain, (![A_158, B_159]: (m1_pre_topc('#skF_3'(A_158, B_159), A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | v1_xboole_0(B_159) | ~l1_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.47/1.89  tff(c_833, plain, (m1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_167, c_827])).
% 4.47/1.89  tff(c_843, plain, (m1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_833])).
% 4.47/1.89  tff(c_844, plain, (m1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_117, c_843])).
% 4.47/1.89  tff(c_1092, plain, (![A_191, B_192, C_193]: (k1_tex_2(A_191, B_192)=C_193 | u1_struct_0(C_193)!=k6_domain_1(u1_struct_0(A_191), B_192) | ~m1_pre_topc(C_193, A_191) | ~v1_pre_topc(C_193) | v2_struct_0(C_193) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~l1_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.47/1.89  tff(c_1106, plain, (![C_193]: (k1_tex_2('#skF_4', '#skF_5')=C_193 | u1_struct_0(C_193)!=k1_tarski('#skF_5') | ~m1_pre_topc(C_193, '#skF_4') | ~v1_pre_topc(C_193) | v2_struct_0(C_193) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_1092])).
% 4.47/1.89  tff(c_1114, plain, (![C_193]: (k1_tex_2('#skF_4', '#skF_5')=C_193 | u1_struct_0(C_193)!=k1_tarski('#skF_5') | ~m1_pre_topc(C_193, '#skF_4') | ~v1_pre_topc(C_193) | v2_struct_0(C_193) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1106])).
% 4.47/1.89  tff(c_1116, plain, (![C_194]: (k1_tex_2('#skF_4', '#skF_5')=C_194 | u1_struct_0(C_194)!=k1_tarski('#skF_5') | ~m1_pre_topc(C_194, '#skF_4') | ~v1_pre_topc(C_194) | v2_struct_0(C_194))), inference(negUnitSimplification, [status(thm)], [c_64, c_1114])).
% 4.47/1.89  tff(c_1123, plain, ('#skF_3'('#skF_4', k1_tarski('#skF_5'))=k1_tex_2('#skF_4', '#skF_5') | u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))!=k1_tarski('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_844, c_1116])).
% 4.47/1.89  tff(c_1130, plain, ('#skF_3'('#skF_4', k1_tarski('#skF_5'))=k1_tex_2('#skF_4', '#skF_5') | v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_364, c_1123])).
% 4.47/1.89  tff(c_1131, plain, ('#skF_3'('#skF_4', k1_tarski('#skF_5'))=k1_tex_2('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_333, c_1130])).
% 4.47/1.89  tff(c_1141, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_844])).
% 4.47/1.89  tff(c_1143, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_333])).
% 4.47/1.89  tff(c_439, plain, (![A_114, B_115]: (v1_tdlat_3(k1_tex_2(A_114, B_115)) | ~v2_pre_topc(k1_tex_2(A_114, B_115)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.47/1.89  tff(c_448, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_5')) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_439])).
% 4.47/1.89  tff(c_452, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_5')) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_448])).
% 4.47/1.89  tff(c_453, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_5')) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_452])).
% 4.47/1.89  tff(c_454, plain, (~v2_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_453])).
% 4.47/1.89  tff(c_455, plain, (![A_116, B_117]: (m1_pre_topc('#skF_3'(A_116, B_117), A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(B_117) | ~l1_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.47/1.89  tff(c_461, plain, (m1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_167, c_455])).
% 4.47/1.89  tff(c_471, plain, (m1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_461])).
% 4.47/1.89  tff(c_472, plain, (m1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_117, c_471])).
% 4.47/1.89  tff(c_754, plain, (![A_152, B_153, C_154]: (k1_tex_2(A_152, B_153)=C_154 | u1_struct_0(C_154)!=k6_domain_1(u1_struct_0(A_152), B_153) | ~m1_pre_topc(C_154, A_152) | ~v1_pre_topc(C_154) | v2_struct_0(C_154) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.47/1.89  tff(c_768, plain, (![C_154]: (k1_tex_2('#skF_4', '#skF_5')=C_154 | u1_struct_0(C_154)!=k1_tarski('#skF_5') | ~m1_pre_topc(C_154, '#skF_4') | ~v1_pre_topc(C_154) | v2_struct_0(C_154) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_754])).
% 4.47/1.89  tff(c_776, plain, (![C_154]: (k1_tex_2('#skF_4', '#skF_5')=C_154 | u1_struct_0(C_154)!=k1_tarski('#skF_5') | ~m1_pre_topc(C_154, '#skF_4') | ~v1_pre_topc(C_154) | v2_struct_0(C_154) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_768])).
% 4.47/1.89  tff(c_778, plain, (![C_155]: (k1_tex_2('#skF_4', '#skF_5')=C_155 | u1_struct_0(C_155)!=k1_tarski('#skF_5') | ~m1_pre_topc(C_155, '#skF_4') | ~v1_pre_topc(C_155) | v2_struct_0(C_155))), inference(negUnitSimplification, [status(thm)], [c_64, c_776])).
% 4.47/1.89  tff(c_785, plain, ('#skF_3'('#skF_4', k1_tarski('#skF_5'))=k1_tex_2('#skF_4', '#skF_5') | u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))!=k1_tarski('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_472, c_778])).
% 4.47/1.89  tff(c_792, plain, ('#skF_3'('#skF_4', k1_tarski('#skF_5'))=k1_tex_2('#skF_4', '#skF_5') | v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_364, c_785])).
% 4.47/1.89  tff(c_793, plain, ('#skF_3'('#skF_4', k1_tarski('#skF_5'))=k1_tex_2('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_333, c_792])).
% 4.47/1.89  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.47/1.89  tff(c_22, plain, (![B_16, A_14]: (v2_pre_topc(B_16) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.47/1.89  tff(c_479, plain, (v2_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_472, c_22])).
% 4.47/1.89  tff(c_485, plain, (v2_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_479])).
% 4.47/1.89  tff(c_803, plain, (v2_pre_topc(k1_tex_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_793, c_485])).
% 4.47/1.89  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_454, c_803])).
% 4.47/1.89  tff(c_810, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_453])).
% 4.47/1.89  tff(c_1142, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_5'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_364])).
% 4.47/1.89  tff(c_52, plain, (![B_47, A_43]: (v2_tex_2(u1_struct_0(B_47), A_43) | ~v1_tdlat_3(B_47) | ~m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_47, A_43) | v2_struct_0(B_47) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.47/1.89  tff(c_1221, plain, (![A_43]: (v2_tex_2(u1_struct_0(k1_tex_2('#skF_4', '#skF_5')), A_43) | ~v1_tdlat_3(k1_tex_2('#skF_4', '#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), A_43) | v2_struct_0(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(superposition, [status(thm), theory('equality')], [c_1142, c_52])).
% 4.47/1.89  tff(c_1270, plain, (![A_43]: (v2_tex_2(k1_tarski('#skF_5'), A_43) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), A_43) | v2_struct_0(k1_tex_2('#skF_4', '#skF_5')) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_810, c_1142, c_1221])).
% 4.47/1.89  tff(c_1729, plain, (![A_228]: (v2_tex_2(k1_tarski('#skF_5'), A_228) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), A_228) | ~l1_pre_topc(A_228) | v2_struct_0(A_228))), inference(negUnitSimplification, [status(thm)], [c_1143, c_1270])).
% 4.47/1.89  tff(c_1744, plain, (v2_tex_2(k1_tarski('#skF_5'), '#skF_4') | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_167, c_1729])).
% 4.47/1.89  tff(c_1753, plain, (v2_tex_2(k1_tarski('#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1141, c_1744])).
% 4.47/1.89  tff(c_1755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_158, c_1753])).
% 4.47/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.89  
% 4.47/1.89  Inference rules
% 4.47/1.89  ----------------------
% 4.47/1.89  #Ref     : 0
% 4.47/1.89  #Sup     : 349
% 4.47/1.89  #Fact    : 0
% 4.47/1.89  #Define  : 0
% 4.47/1.89  #Split   : 4
% 4.47/1.89  #Chain   : 0
% 4.47/1.89  #Close   : 0
% 4.47/1.89  
% 4.47/1.89  Ordering : KBO
% 4.47/1.89  
% 4.47/1.89  Simplification rules
% 4.47/1.89  ----------------------
% 4.47/1.89  #Subsume      : 54
% 4.47/1.89  #Demod        : 266
% 4.47/1.89  #Tautology    : 81
% 4.47/1.89  #SimpNegUnit  : 118
% 4.47/1.89  #BackRed      : 28
% 4.47/1.89  
% 4.47/1.89  #Partial instantiations: 0
% 4.47/1.89  #Strategies tried      : 1
% 4.47/1.89  
% 4.47/1.89  Timing (in seconds)
% 4.47/1.89  ----------------------
% 4.47/1.89  Preprocessing        : 0.38
% 4.47/1.89  Parsing              : 0.20
% 4.47/1.89  CNF conversion       : 0.03
% 4.47/1.89  Main loop            : 0.68
% 4.47/1.89  Inferencing          : 0.23
% 4.47/1.89  Reduction            : 0.22
% 4.47/1.89  Demodulation         : 0.14
% 4.47/1.89  BG Simplification    : 0.03
% 4.47/1.89  Subsumption          : 0.13
% 4.47/1.89  Abstraction          : 0.04
% 4.47/1.89  MUC search           : 0.00
% 4.47/1.89  Cooper               : 0.00
% 4.47/1.89  Total                : 1.09
% 4.47/1.89  Index Insertion      : 0.00
% 4.47/1.89  Index Deletion       : 0.00
% 4.47/1.89  Index Matching       : 0.00
% 4.47/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
