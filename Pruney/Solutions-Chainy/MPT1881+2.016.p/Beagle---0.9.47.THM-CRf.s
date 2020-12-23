%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:08 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 639 expanded)
%              Number of leaves         :   38 ( 232 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 (1641 expanded)
%              Number of equality atoms :   32 ( 227 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14] : ~ v1_subset_1(k2_subset_1(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    ! [A_14] : ~ v1_subset_1(A_14,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_18,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_438,plain,(
    ! [A_101] :
      ( u1_struct_0(A_101) = k2_struct_0(A_101)
      | ~ l1_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_453,plain,(
    ! [A_104] :
      ( u1_struct_0(A_104) = k2_struct_0(A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_438])).

tff(c_457,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_453])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_459,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_48])).

tff(c_58,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_79,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_81,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_64,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_96,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64])).

tff(c_97,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_96])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48])).

tff(c_107,plain,(
    ! [B_49,A_50] :
      ( v1_subset_1(B_49,A_50)
      | B_49 = A_50
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_110,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_107])).

tff(c_116,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_110])).

tff(c_20,plain,(
    ! [A_17] :
      ( k2_pre_topc(A_17,k2_struct_0(A_17)) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_132,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_116,c_128])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_123,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_90])).

tff(c_190,plain,(
    ! [B_62,A_63] :
      ( v1_tops_1(B_62,A_63)
      | k2_pre_topc(A_63,B_62) != u1_struct_0(A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_193,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_3')
      | k2_pre_topc('#skF_3',B_62) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_62,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_190])).

tff(c_201,plain,(
    ! [B_64] :
      ( v1_tops_1(B_64,'#skF_3')
      | k2_pre_topc('#skF_3',B_64) != '#skF_4'
      | ~ m1_subset_1(B_64,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_123,c_193])).

tff(c_205,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_201])).

tff(c_208,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_205])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_219,plain,(
    ! [B_66,A_67] :
      ( v2_tex_2(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v1_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_222,plain,(
    ! [B_66] :
      ( v2_tex_2(B_66,'#skF_3')
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_219])).

tff(c_228,plain,(
    ! [B_66] :
      ( v2_tex_2(B_66,'#skF_3')
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_222])).

tff(c_231,plain,(
    ! [B_68] :
      ( v2_tex_2(B_68,'#skF_3')
      | ~ m1_subset_1(B_68,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_228])).

tff(c_236,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_231])).

tff(c_396,plain,(
    ! [B_98,A_99] :
      ( v3_tex_2(B_98,A_99)
      | ~ v2_tex_2(B_98,A_99)
      | ~ v1_tops_1(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_403,plain,(
    ! [B_98] :
      ( v3_tex_2(B_98,'#skF_3')
      | ~ v2_tex_2(B_98,'#skF_3')
      | ~ v1_tops_1(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_396])).

tff(c_410,plain,(
    ! [B_98] :
      ( v3_tex_2(B_98,'#skF_3')
      | ~ v2_tex_2(B_98,'#skF_3')
      | ~ v1_tops_1(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_403])).

tff(c_414,plain,(
    ! [B_100] :
      ( v3_tex_2(B_100,'#skF_3')
      | ~ v2_tex_2(B_100,'#skF_3')
      | ~ v1_tops_1(B_100,'#skF_3')
      | ~ m1_subset_1(B_100,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_410])).

tff(c_422,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_414])).

tff(c_426,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_236,c_422])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_426])).

tff(c_430,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_478,plain,(
    ! [B_110,A_111] :
      ( v2_tex_2(B_110,A_111)
      | ~ v3_tex_2(B_110,A_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_489,plain,(
    ! [A_112] :
      ( v2_tex_2(u1_struct_0(A_112),A_112)
      | ~ v3_tex_2(u1_struct_0(A_112),A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_66,c_478])).

tff(c_492,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_489])).

tff(c_494,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_457,c_492])).

tff(c_495,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_508,plain,(
    ! [B_114,A_115] :
      ( v1_tops_1(B_114,A_115)
      | k2_pre_topc(A_115,B_114) != u1_struct_0(A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_519,plain,(
    ! [A_116] :
      ( v1_tops_1(u1_struct_0(A_116),A_116)
      | k2_pre_topc(A_116,u1_struct_0(A_116)) != u1_struct_0(A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_66,c_508])).

tff(c_522,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_519])).

tff(c_524,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_457,c_457,c_522])).

tff(c_536,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_539,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_536])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_539])).

tff(c_544,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_598,plain,(
    ! [B_122,A_123] :
      ( v2_tex_2(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v1_tdlat_3(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_601,plain,(
    ! [B_122] :
      ( v2_tex_2(B_122,'#skF_3')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_598])).

tff(c_607,plain,(
    ! [B_122] :
      ( v2_tex_2(B_122,'#skF_3')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_601])).

tff(c_610,plain,(
    ! [B_124] :
      ( v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_607])).

tff(c_620,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_610])).

tff(c_825,plain,(
    ! [B_154,A_155] :
      ( v3_tex_2(B_154,A_155)
      | ~ v2_tex_2(B_154,A_155)
      | ~ v1_tops_1(B_154,A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_832,plain,(
    ! [B_154] :
      ( v3_tex_2(B_154,'#skF_3')
      | ~ v2_tex_2(B_154,'#skF_3')
      | ~ v1_tops_1(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_825])).

tff(c_839,plain,(
    ! [B_154] :
      ( v3_tex_2(B_154,'#skF_3')
      | ~ v2_tex_2(B_154,'#skF_3')
      | ~ v1_tops_1(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_832])).

tff(c_842,plain,(
    ! [B_156] :
      ( v3_tex_2(B_156,'#skF_3')
      | ~ v2_tex_2(B_156,'#skF_3')
      | ~ v1_tops_1(B_156,'#skF_3')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839])).

tff(c_853,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_842])).

tff(c_860,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_620,c_853])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_860])).

tff(c_863,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_1591,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_1'(A_242,B_243,C_244),B_243)
      | r1_tarski(B_243,C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(A_242))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1819,plain,(
    ! [A_266,B_267,C_268,A_269] :
      ( r2_hidden('#skF_1'(A_266,B_267,C_268),A_269)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(A_269))
      | r1_tarski(B_267,C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(A_266))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(A_266)) ) ),
    inference(resolution,[status(thm)],[c_1591,c_6])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1828,plain,(
    ! [B_270,A_271,A_272] :
      ( ~ m1_subset_1(B_270,k1_zfmisc_1(A_271))
      | r1_tarski(B_270,A_271)
      | ~ m1_subset_1(A_271,k1_zfmisc_1(A_272))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(A_272)) ) ),
    inference(resolution,[status(thm)],[c_1819,c_8])).

tff(c_1843,plain,(
    ! [A_272] :
      ( r1_tarski('#skF_4',k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(A_272))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_272)) ) ),
    inference(resolution,[status(thm)],[c_459,c_1828])).

tff(c_1847,plain,(
    ! [A_273] :
      ( ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(A_273))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_273)) ) ),
    inference(splitLeft,[status(thm)],[c_1843])).

tff(c_1851,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_66,c_1847])).

tff(c_1855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_1851])).

tff(c_1856,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1843])).

tff(c_40,plain,(
    ! [C_33,B_30,A_24] :
      ( C_33 = B_30
      | ~ r1_tarski(B_30,C_33)
      | ~ v2_tex_2(C_33,A_24)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ v3_tex_2(B_30,A_24)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1859,plain,(
    ! [A_24] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_24)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ v3_tex_2('#skF_4',A_24)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_1856,c_40])).

tff(c_1914,plain,(
    ! [A_279] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_279)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ v3_tex_2('#skF_4',A_279)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279) ) ),
    inference(splitLeft,[status(thm)],[c_1859])).

tff(c_1917,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_1914])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_459,c_457,c_430,c_66,c_863,c_1917])).

tff(c_1921,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_429,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_458,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_429])).

tff(c_1941,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_458])).

tff(c_1949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:07:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.77  
% 4.32/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.78  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.32/1.78  
% 4.32/1.78  %Foreground sorts:
% 4.32/1.78  
% 4.32/1.78  
% 4.32/1.78  %Background operators:
% 4.32/1.78  
% 4.32/1.78  
% 4.32/1.78  %Foreground operators:
% 4.32/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.32/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.78  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.32/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.32/1.78  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.32/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.78  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.32/1.78  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.32/1.78  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.32/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.32/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.32/1.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.32/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.32/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.32/1.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.32/1.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.32/1.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.32/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.78  
% 4.40/1.80  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.40/1.80  tff(f_53, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.40/1.80  tff(f_153, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.40/1.80  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.40/1.80  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.40/1.80  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.40/1.80  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 4.40/1.80  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.40/1.80  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.40/1.80  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.40/1.80  tff(f_135, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.40/1.80  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.40/1.80  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 4.40/1.80  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.40/1.80  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.40/1.80  tff(c_14, plain, (![A_14]: (~v1_subset_1(k2_subset_1(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.40/1.80  tff(c_65, plain, (![A_14]: (~v1_subset_1(A_14, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 4.40/1.80  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.40/1.80  tff(c_438, plain, (![A_101]: (u1_struct_0(A_101)=k2_struct_0(A_101) | ~l1_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.80  tff(c_453, plain, (![A_104]: (u1_struct_0(A_104)=k2_struct_0(A_104) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_18, c_438])).
% 4.40/1.80  tff(c_457, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_453])).
% 4.40/1.80  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_459, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_48])).
% 4.40/1.80  tff(c_58, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_79, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 4.40/1.80  tff(c_81, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.80  tff(c_86, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_18, c_81])).
% 4.40/1.80  tff(c_90, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_86])).
% 4.40/1.80  tff(c_64, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_96, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64])).
% 4.40/1.80  tff(c_97, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_79, c_96])).
% 4.40/1.80  tff(c_91, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48])).
% 4.40/1.80  tff(c_107, plain, (![B_49, A_50]: (v1_subset_1(B_49, A_50) | B_49=A_50 | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.40/1.80  tff(c_110, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_91, c_107])).
% 4.40/1.80  tff(c_116, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_97, c_110])).
% 4.40/1.80  tff(c_20, plain, (![A_17]: (k2_pre_topc(A_17, k2_struct_0(A_17))=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.40/1.80  tff(c_128, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_20])).
% 4.40/1.80  tff(c_132, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_116, c_128])).
% 4.40/1.80  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.40/1.80  tff(c_66, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.40/1.80  tff(c_123, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_90])).
% 4.40/1.80  tff(c_190, plain, (![B_62, A_63]: (v1_tops_1(B_62, A_63) | k2_pre_topc(A_63, B_62)!=u1_struct_0(A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.40/1.80  tff(c_193, plain, (![B_62]: (v1_tops_1(B_62, '#skF_3') | k2_pre_topc('#skF_3', B_62)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_62, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_190])).
% 4.40/1.80  tff(c_201, plain, (![B_64]: (v1_tops_1(B_64, '#skF_3') | k2_pre_topc('#skF_3', B_64)!='#skF_4' | ~m1_subset_1(B_64, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_123, c_193])).
% 4.40/1.80  tff(c_205, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_66, c_201])).
% 4.40/1.80  tff(c_208, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_205])).
% 4.40/1.80  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_52, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.40/1.80  tff(c_219, plain, (![B_66, A_67]: (v2_tex_2(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v1_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.40/1.80  tff(c_222, plain, (![B_66]: (v2_tex_2(B_66, '#skF_3') | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_219])).
% 4.40/1.80  tff(c_228, plain, (![B_66]: (v2_tex_2(B_66, '#skF_3') | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_222])).
% 4.40/1.80  tff(c_231, plain, (![B_68]: (v2_tex_2(B_68, '#skF_3') | ~m1_subset_1(B_68, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_228])).
% 4.40/1.80  tff(c_236, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_231])).
% 4.40/1.80  tff(c_396, plain, (![B_98, A_99]: (v3_tex_2(B_98, A_99) | ~v2_tex_2(B_98, A_99) | ~v1_tops_1(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.40/1.80  tff(c_403, plain, (![B_98]: (v3_tex_2(B_98, '#skF_3') | ~v2_tex_2(B_98, '#skF_3') | ~v1_tops_1(B_98, '#skF_3') | ~m1_subset_1(B_98, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_396])).
% 4.40/1.80  tff(c_410, plain, (![B_98]: (v3_tex_2(B_98, '#skF_3') | ~v2_tex_2(B_98, '#skF_3') | ~v1_tops_1(B_98, '#skF_3') | ~m1_subset_1(B_98, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_403])).
% 4.40/1.80  tff(c_414, plain, (![B_100]: (v3_tex_2(B_100, '#skF_3') | ~v2_tex_2(B_100, '#skF_3') | ~v1_tops_1(B_100, '#skF_3') | ~m1_subset_1(B_100, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_410])).
% 4.40/1.80  tff(c_422, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_414])).
% 4.40/1.80  tff(c_426, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_236, c_422])).
% 4.40/1.80  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_426])).
% 4.40/1.80  tff(c_430, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 4.40/1.80  tff(c_478, plain, (![B_110, A_111]: (v2_tex_2(B_110, A_111) | ~v3_tex_2(B_110, A_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.40/1.80  tff(c_489, plain, (![A_112]: (v2_tex_2(u1_struct_0(A_112), A_112) | ~v3_tex_2(u1_struct_0(A_112), A_112) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_66, c_478])).
% 4.40/1.80  tff(c_492, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_457, c_489])).
% 4.40/1.80  tff(c_494, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_457, c_492])).
% 4.40/1.80  tff(c_495, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_494])).
% 4.40/1.80  tff(c_508, plain, (![B_114, A_115]: (v1_tops_1(B_114, A_115) | k2_pre_topc(A_115, B_114)!=u1_struct_0(A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.40/1.80  tff(c_519, plain, (![A_116]: (v1_tops_1(u1_struct_0(A_116), A_116) | k2_pre_topc(A_116, u1_struct_0(A_116))!=u1_struct_0(A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_66, c_508])).
% 4.40/1.80  tff(c_522, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_457, c_519])).
% 4.40/1.80  tff(c_524, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_457, c_457, c_522])).
% 4.40/1.80  tff(c_536, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_524])).
% 4.40/1.80  tff(c_539, plain, (~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_536])).
% 4.40/1.80  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_539])).
% 4.40/1.80  tff(c_544, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_524])).
% 4.40/1.80  tff(c_598, plain, (![B_122, A_123]: (v2_tex_2(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v1_tdlat_3(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.40/1.80  tff(c_601, plain, (![B_122]: (v2_tex_2(B_122, '#skF_3') | ~m1_subset_1(B_122, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_457, c_598])).
% 4.40/1.80  tff(c_607, plain, (![B_122]: (v2_tex_2(B_122, '#skF_3') | ~m1_subset_1(B_122, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_601])).
% 4.40/1.80  tff(c_610, plain, (![B_124]: (v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_607])).
% 4.40/1.80  tff(c_620, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_610])).
% 4.40/1.80  tff(c_825, plain, (![B_154, A_155]: (v3_tex_2(B_154, A_155) | ~v2_tex_2(B_154, A_155) | ~v1_tops_1(B_154, A_155) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.40/1.80  tff(c_832, plain, (![B_154]: (v3_tex_2(B_154, '#skF_3') | ~v2_tex_2(B_154, '#skF_3') | ~v1_tops_1(B_154, '#skF_3') | ~m1_subset_1(B_154, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_457, c_825])).
% 4.40/1.80  tff(c_839, plain, (![B_154]: (v3_tex_2(B_154, '#skF_3') | ~v2_tex_2(B_154, '#skF_3') | ~v1_tops_1(B_154, '#skF_3') | ~m1_subset_1(B_154, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_832])).
% 4.40/1.80  tff(c_842, plain, (![B_156]: (v3_tex_2(B_156, '#skF_3') | ~v2_tex_2(B_156, '#skF_3') | ~v1_tops_1(B_156, '#skF_3') | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_839])).
% 4.40/1.80  tff(c_853, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_842])).
% 4.40/1.80  tff(c_860, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_620, c_853])).
% 4.40/1.80  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_860])).
% 4.40/1.80  tff(c_863, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_494])).
% 4.40/1.80  tff(c_1591, plain, (![A_242, B_243, C_244]: (r2_hidden('#skF_1'(A_242, B_243, C_244), B_243) | r1_tarski(B_243, C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(A_242)) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.40/1.80  tff(c_6, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.40/1.80  tff(c_1819, plain, (![A_266, B_267, C_268, A_269]: (r2_hidden('#skF_1'(A_266, B_267, C_268), A_269) | ~m1_subset_1(B_267, k1_zfmisc_1(A_269)) | r1_tarski(B_267, C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(A_266)) | ~m1_subset_1(B_267, k1_zfmisc_1(A_266)))), inference(resolution, [status(thm)], [c_1591, c_6])).
% 4.40/1.80  tff(c_8, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.40/1.80  tff(c_1828, plain, (![B_270, A_271, A_272]: (~m1_subset_1(B_270, k1_zfmisc_1(A_271)) | r1_tarski(B_270, A_271) | ~m1_subset_1(A_271, k1_zfmisc_1(A_272)) | ~m1_subset_1(B_270, k1_zfmisc_1(A_272)))), inference(resolution, [status(thm)], [c_1819, c_8])).
% 4.40/1.80  tff(c_1843, plain, (![A_272]: (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(A_272)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_272)))), inference(resolution, [status(thm)], [c_459, c_1828])).
% 4.40/1.80  tff(c_1847, plain, (![A_273]: (~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(A_273)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_273)))), inference(splitLeft, [status(thm)], [c_1843])).
% 4.40/1.80  tff(c_1851, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_1847])).
% 4.40/1.80  tff(c_1855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_1851])).
% 4.40/1.80  tff(c_1856, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1843])).
% 4.40/1.80  tff(c_40, plain, (![C_33, B_30, A_24]: (C_33=B_30 | ~r1_tarski(B_30, C_33) | ~v2_tex_2(C_33, A_24) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_24))) | ~v3_tex_2(B_30, A_24) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.40/1.80  tff(c_1859, plain, (![A_24]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_24) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_24))) | ~v3_tex_2('#skF_4', A_24) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_1856, c_40])).
% 4.40/1.80  tff(c_1914, plain, (![A_279]: (~v2_tex_2(k2_struct_0('#skF_3'), A_279) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_279))) | ~v3_tex_2('#skF_4', A_279) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279))), inference(splitLeft, [status(thm)], [c_1859])).
% 4.40/1.80  tff(c_1917, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_457, c_1914])).
% 4.40/1.80  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_459, c_457, c_430, c_66, c_863, c_1917])).
% 4.40/1.80  tff(c_1921, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1859])).
% 4.40/1.80  tff(c_429, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 4.40/1.80  tff(c_458, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_429])).
% 4.40/1.80  tff(c_1941, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_458])).
% 4.40/1.80  tff(c_1949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1941])).
% 4.40/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.80  
% 4.40/1.80  Inference rules
% 4.40/1.80  ----------------------
% 4.40/1.80  #Ref     : 0
% 4.40/1.80  #Sup     : 343
% 4.40/1.80  #Fact    : 0
% 4.40/1.80  #Define  : 0
% 4.40/1.80  #Split   : 11
% 4.40/1.80  #Chain   : 0
% 4.40/1.80  #Close   : 0
% 4.40/1.80  
% 4.40/1.80  Ordering : KBO
% 4.40/1.80  
% 4.40/1.80  Simplification rules
% 4.40/1.80  ----------------------
% 4.40/1.80  #Subsume      : 21
% 4.40/1.80  #Demod        : 409
% 4.40/1.80  #Tautology    : 121
% 4.40/1.80  #SimpNegUnit  : 36
% 4.40/1.80  #BackRed      : 47
% 4.40/1.80  
% 4.40/1.80  #Partial instantiations: 0
% 4.40/1.80  #Strategies tried      : 1
% 4.40/1.80  
% 4.40/1.80  Timing (in seconds)
% 4.40/1.80  ----------------------
% 4.40/1.80  Preprocessing        : 0.36
% 4.40/1.80  Parsing              : 0.20
% 4.40/1.80  CNF conversion       : 0.02
% 4.40/1.80  Main loop            : 0.63
% 4.40/1.80  Inferencing          : 0.23
% 4.40/1.80  Reduction            : 0.19
% 4.40/1.80  Demodulation         : 0.13
% 4.40/1.80  BG Simplification    : 0.03
% 4.40/1.80  Subsumption          : 0.13
% 4.40/1.80  Abstraction          : 0.03
% 4.40/1.80  MUC search           : 0.00
% 4.40/1.80  Cooper               : 0.00
% 4.40/1.80  Total                : 1.05
% 4.40/1.80  Index Insertion      : 0.00
% 4.40/1.80  Index Deletion       : 0.00
% 4.40/1.80  Index Matching       : 0.00
% 4.40/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
