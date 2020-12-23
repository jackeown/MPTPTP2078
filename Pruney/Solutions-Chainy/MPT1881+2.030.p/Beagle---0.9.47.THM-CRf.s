%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:10 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 402 expanded)
%              Number of leaves         :   35 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  241 (1019 expanded)
%              Number of equality atoms :   18 ( 120 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_86,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_24,plain,(
    ! [B_17] :
      ( ~ v1_subset_1(B_17,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,(
    ! [B_17] : ~ v1_subset_1(B_17,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_24])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_474,plain,(
    ! [A_124] :
      ( u1_struct_0(A_124) = k2_struct_0(A_124)
      | ~ l1_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_479,plain,(
    ! [A_125] :
      ( u1_struct_0(A_125) = k2_struct_0(A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_16,c_474])).

tff(c_483,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_479])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_486,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_42])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_74,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_87,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_52])).

tff(c_76,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_86,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_88,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_74])).

tff(c_89,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42])).

tff(c_106,plain,(
    ! [B_51,A_52] :
      ( v1_subset_1(B_51,A_52)
      | B_51 = A_52
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_89,c_106])).

tff(c_115,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_109])).

tff(c_18,plain,(
    ! [A_14] :
      ( v1_tops_1(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_18])).

tff(c_131,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_122,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_86])).

tff(c_198,plain,(
    ! [B_72,A_73] :
      ( v2_tex_2(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v1_tdlat_3(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_201,plain,(
    ! [B_72] :
      ( v2_tex_2(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_198])).

tff(c_207,plain,(
    ! [B_72] :
      ( v2_tex_2(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_201])).

tff(c_210,plain,(
    ! [B_74] :
      ( v2_tex_2(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_207])).

tff(c_215,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_210])).

tff(c_426,plain,(
    ! [B_117,A_118] :
      ( v3_tex_2(B_117,A_118)
      | ~ v2_tex_2(B_117,A_118)
      | ~ v1_tops_1(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_429,plain,(
    ! [B_117] :
      ( v3_tex_2(B_117,'#skF_3')
      | ~ v2_tex_2(B_117,'#skF_3')
      | ~ v1_tops_1(B_117,'#skF_3')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_426])).

tff(c_435,plain,(
    ! [B_117] :
      ( v3_tex_2(B_117,'#skF_3')
      | ~ v2_tex_2(B_117,'#skF_3')
      | ~ v1_tops_1(B_117,'#skF_3')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_429])).

tff(c_457,plain,(
    ! [B_121] :
      ( v3_tex_2(B_121,'#skF_3')
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ v1_tops_1(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_435])).

tff(c_461,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_457])).

tff(c_464,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_215,c_461])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_464])).

tff(c_467,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_531,plain,(
    ! [B_142,A_143] :
      ( v2_tex_2(B_142,A_143)
      | ~ v3_tex_2(B_142,A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_542,plain,(
    ! [A_144] :
      ( v2_tex_2(u1_struct_0(A_144),A_144)
      | ~ v3_tex_2(u1_struct_0(A_144),A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_59,c_531])).

tff(c_545,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_542])).

tff(c_547,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_483,c_545])).

tff(c_548,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_590,plain,(
    ! [B_155,A_156] :
      ( v2_tex_2(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v1_tdlat_3(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_593,plain,(
    ! [B_155] :
      ( v2_tex_2(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_590])).

tff(c_599,plain,(
    ! [B_155] :
      ( v2_tex_2(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_593])).

tff(c_602,plain,(
    ! [B_157] :
      ( v2_tex_2(B_157,'#skF_3')
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_599])).

tff(c_612,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_602])).

tff(c_973,plain,(
    ! [B_220,A_221] :
      ( v3_tex_2(B_220,A_221)
      | ~ v2_tex_2(B_220,A_221)
      | ~ v1_tops_1(B_220,A_221)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_976,plain,(
    ! [B_220] :
      ( v3_tex_2(B_220,'#skF_3')
      | ~ v2_tex_2(B_220,'#skF_3')
      | ~ v1_tops_1(B_220,'#skF_3')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_973])).

tff(c_982,plain,(
    ! [B_220] :
      ( v3_tex_2(B_220,'#skF_3')
      | ~ v2_tex_2(B_220,'#skF_3')
      | ~ v1_tops_1(B_220,'#skF_3')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_976])).

tff(c_1010,plain,(
    ! [B_223] :
      ( v3_tex_2(B_223,'#skF_3')
      | ~ v2_tex_2(B_223,'#skF_3')
      | ~ v1_tops_1(B_223,'#skF_3')
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_982])).

tff(c_1017,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_1010])).

tff(c_1023,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_1017])).

tff(c_1024,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_1023])).

tff(c_1027,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1024])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1027])).

tff(c_1032,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_515,plain,(
    ! [C_136,A_137,B_138] :
      ( r2_hidden(C_136,A_137)
      | ~ r2_hidden(C_136,B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1048,plain,(
    ! [A_225,B_226,A_227] :
      ( r2_hidden('#skF_1'(A_225,B_226),A_227)
      | ~ m1_subset_1(A_225,k1_zfmisc_1(A_227))
      | r1_tarski(A_225,B_226) ) ),
    inference(resolution,[status(thm)],[c_6,c_515])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1072,plain,(
    ! [A_230,A_231] :
      ( ~ m1_subset_1(A_230,k1_zfmisc_1(A_231))
      | r1_tarski(A_230,A_231) ) ),
    inference(resolution,[status(thm)],[c_1048,c_4])).

tff(c_1079,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_486,c_1072])).

tff(c_2261,plain,(
    ! [C_389,B_390,A_391] :
      ( C_389 = B_390
      | ~ r1_tarski(B_390,C_389)
      | ~ v2_tex_2(C_389,A_391)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ v3_tex_2(B_390,A_391)
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ l1_pre_topc(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2281,plain,(
    ! [A_391] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_391)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ v3_tex_2('#skF_4',A_391)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ l1_pre_topc(A_391) ) ),
    inference(resolution,[status(thm)],[c_1079,c_2261])).

tff(c_2828,plain,(
    ! [A_466] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_466)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ v3_tex_2('#skF_4',A_466)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ l1_pre_topc(A_466) ) ),
    inference(splitLeft,[status(thm)],[c_2281])).

tff(c_2831,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_2828])).

tff(c_2834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_486,c_483,c_467,c_59,c_1032,c_2831])).

tff(c_2835,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2281])).

tff(c_470,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_52])).

tff(c_485,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_470])).

tff(c_2883,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_485])).

tff(c_2891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_2883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.92  
% 7.69/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.93  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.69/2.93  
% 7.69/2.93  %Foreground sorts:
% 7.69/2.93  
% 7.69/2.93  
% 7.69/2.93  %Background operators:
% 7.69/2.93  
% 7.69/2.93  
% 7.69/2.93  %Foreground operators:
% 7.69/2.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.69/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.69/2.93  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.69/2.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.69/2.93  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.69/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.69/2.93  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.69/2.93  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.69/2.93  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.69/2.93  tff('#skF_3', type, '#skF_3': $i).
% 7.69/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.69/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.93  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.69/2.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.69/2.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.69/2.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.69/2.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.69/2.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.69/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.93  
% 7.69/2.96  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.69/2.96  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.69/2.96  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 7.69/2.96  tff(f_134, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 7.69/2.96  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.69/2.96  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.69/2.96  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => v1_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_tops_1)).
% 7.69/2.96  tff(f_100, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 7.69/2.96  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 7.69/2.96  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 7.69/2.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.69/2.96  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.69/2.96  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.69/2.96  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.69/2.96  tff(c_59, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.69/2.96  tff(c_24, plain, (![B_17]: (~v1_subset_1(B_17, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.69/2.96  tff(c_61, plain, (![B_17]: (~v1_subset_1(B_17, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_24])).
% 7.69/2.96  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.69/2.96  tff(c_474, plain, (![A_124]: (u1_struct_0(A_124)=k2_struct_0(A_124) | ~l1_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.69/2.96  tff(c_479, plain, (![A_125]: (u1_struct_0(A_125)=k2_struct_0(A_125) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_16, c_474])).
% 7.69/2.96  tff(c_483, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_479])).
% 7.69/2.96  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_486, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_42])).
% 7.69/2.96  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_74, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 7.69/2.96  tff(c_52, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_87, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_52])).
% 7.69/2.96  tff(c_76, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.69/2.96  tff(c_82, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_16, c_76])).
% 7.69/2.96  tff(c_86, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_82])).
% 7.69/2.96  tff(c_88, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_74])).
% 7.69/2.96  tff(c_89, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42])).
% 7.69/2.96  tff(c_106, plain, (![B_51, A_52]: (v1_subset_1(B_51, A_52) | B_51=A_52 | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.69/2.96  tff(c_109, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_89, c_106])).
% 7.69/2.96  tff(c_115, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_88, c_109])).
% 7.69/2.96  tff(c_18, plain, (![A_14]: (v1_tops_1(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.69/2.96  tff(c_127, plain, (v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_18])).
% 7.69/2.96  tff(c_131, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127])).
% 7.69/2.96  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_46, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.69/2.96  tff(c_122, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_86])).
% 7.69/2.96  tff(c_198, plain, (![B_72, A_73]: (v2_tex_2(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v1_tdlat_3(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.69/2.96  tff(c_201, plain, (![B_72]: (v2_tex_2(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_198])).
% 7.69/2.96  tff(c_207, plain, (![B_72]: (v2_tex_2(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_201])).
% 7.69/2.96  tff(c_210, plain, (![B_74]: (v2_tex_2(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_207])).
% 7.69/2.96  tff(c_215, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_59, c_210])).
% 7.69/2.96  tff(c_426, plain, (![B_117, A_118]: (v3_tex_2(B_117, A_118) | ~v2_tex_2(B_117, A_118) | ~v1_tops_1(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.69/2.96  tff(c_429, plain, (![B_117]: (v3_tex_2(B_117, '#skF_3') | ~v2_tex_2(B_117, '#skF_3') | ~v1_tops_1(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_426])).
% 7.69/2.96  tff(c_435, plain, (![B_117]: (v3_tex_2(B_117, '#skF_3') | ~v2_tex_2(B_117, '#skF_3') | ~v1_tops_1(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_429])).
% 7.69/2.96  tff(c_457, plain, (![B_121]: (v3_tex_2(B_121, '#skF_3') | ~v2_tex_2(B_121, '#skF_3') | ~v1_tops_1(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_435])).
% 7.69/2.96  tff(c_461, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_59, c_457])).
% 7.69/2.96  tff(c_464, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_215, c_461])).
% 7.69/2.96  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_464])).
% 7.69/2.96  tff(c_467, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 7.69/2.96  tff(c_531, plain, (![B_142, A_143]: (v2_tex_2(B_142, A_143) | ~v3_tex_2(B_142, A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.69/2.96  tff(c_542, plain, (![A_144]: (v2_tex_2(u1_struct_0(A_144), A_144) | ~v3_tex_2(u1_struct_0(A_144), A_144) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_59, c_531])).
% 7.69/2.96  tff(c_545, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_483, c_542])).
% 7.69/2.96  tff(c_547, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_483, c_545])).
% 7.69/2.96  tff(c_548, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_547])).
% 7.69/2.96  tff(c_590, plain, (![B_155, A_156]: (v2_tex_2(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v1_tdlat_3(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.69/2.96  tff(c_593, plain, (![B_155]: (v2_tex_2(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_590])).
% 7.69/2.96  tff(c_599, plain, (![B_155]: (v2_tex_2(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_593])).
% 7.69/2.96  tff(c_602, plain, (![B_157]: (v2_tex_2(B_157, '#skF_3') | ~m1_subset_1(B_157, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_599])).
% 7.69/2.96  tff(c_612, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_59, c_602])).
% 7.69/2.96  tff(c_973, plain, (![B_220, A_221]: (v3_tex_2(B_220, A_221) | ~v2_tex_2(B_220, A_221) | ~v1_tops_1(B_220, A_221) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.69/2.96  tff(c_976, plain, (![B_220]: (v3_tex_2(B_220, '#skF_3') | ~v2_tex_2(B_220, '#skF_3') | ~v1_tops_1(B_220, '#skF_3') | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_973])).
% 7.69/2.96  tff(c_982, plain, (![B_220]: (v3_tex_2(B_220, '#skF_3') | ~v2_tex_2(B_220, '#skF_3') | ~v1_tops_1(B_220, '#skF_3') | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_976])).
% 7.69/2.96  tff(c_1010, plain, (![B_223]: (v3_tex_2(B_223, '#skF_3') | ~v2_tex_2(B_223, '#skF_3') | ~v1_tops_1(B_223, '#skF_3') | ~m1_subset_1(B_223, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_982])).
% 7.69/2.96  tff(c_1017, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_59, c_1010])).
% 7.69/2.96  tff(c_1023, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_1017])).
% 7.69/2.96  tff(c_1024, plain, (~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_548, c_1023])).
% 7.69/2.96  tff(c_1027, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1024])).
% 7.69/2.96  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1027])).
% 7.69/2.96  tff(c_1032, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_547])).
% 7.69/2.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.96  tff(c_515, plain, (![C_136, A_137, B_138]: (r2_hidden(C_136, A_137) | ~r2_hidden(C_136, B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.69/2.96  tff(c_1048, plain, (![A_225, B_226, A_227]: (r2_hidden('#skF_1'(A_225, B_226), A_227) | ~m1_subset_1(A_225, k1_zfmisc_1(A_227)) | r1_tarski(A_225, B_226))), inference(resolution, [status(thm)], [c_6, c_515])).
% 7.69/2.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.96  tff(c_1072, plain, (![A_230, A_231]: (~m1_subset_1(A_230, k1_zfmisc_1(A_231)) | r1_tarski(A_230, A_231))), inference(resolution, [status(thm)], [c_1048, c_4])).
% 7.69/2.96  tff(c_1079, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_486, c_1072])).
% 7.69/2.96  tff(c_2261, plain, (![C_389, B_390, A_391]: (C_389=B_390 | ~r1_tarski(B_390, C_389) | ~v2_tex_2(C_389, A_391) | ~m1_subset_1(C_389, k1_zfmisc_1(u1_struct_0(A_391))) | ~v3_tex_2(B_390, A_391) | ~m1_subset_1(B_390, k1_zfmisc_1(u1_struct_0(A_391))) | ~l1_pre_topc(A_391))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.69/2.96  tff(c_2281, plain, (![A_391]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_391) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_391))) | ~v3_tex_2('#skF_4', A_391) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_391))) | ~l1_pre_topc(A_391))), inference(resolution, [status(thm)], [c_1079, c_2261])).
% 7.69/2.96  tff(c_2828, plain, (![A_466]: (~v2_tex_2(k2_struct_0('#skF_3'), A_466) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_466))) | ~v3_tex_2('#skF_4', A_466) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_466))) | ~l1_pre_topc(A_466))), inference(splitLeft, [status(thm)], [c_2281])).
% 7.69/2.96  tff(c_2831, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_483, c_2828])).
% 7.69/2.96  tff(c_2834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_486, c_483, c_467, c_59, c_1032, c_2831])).
% 7.69/2.96  tff(c_2835, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2281])).
% 7.69/2.96  tff(c_470, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_52])).
% 7.69/2.96  tff(c_485, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_470])).
% 7.69/2.96  tff(c_2883, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2835, c_485])).
% 7.69/2.96  tff(c_2891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_2883])).
% 7.69/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.96  
% 7.69/2.96  Inference rules
% 7.69/2.96  ----------------------
% 7.69/2.96  #Ref     : 0
% 7.69/2.96  #Sup     : 635
% 7.69/2.96  #Fact    : 0
% 7.69/2.96  #Define  : 0
% 7.69/2.96  #Split   : 9
% 7.69/2.96  #Chain   : 0
% 7.69/2.96  #Close   : 0
% 7.69/2.96  
% 7.69/2.96  Ordering : KBO
% 7.69/2.96  
% 7.69/2.96  Simplification rules
% 7.69/2.96  ----------------------
% 7.69/2.96  #Subsume      : 263
% 7.69/2.96  #Demod        : 403
% 7.69/2.96  #Tautology    : 102
% 7.69/2.96  #SimpNegUnit  : 30
% 7.69/2.96  #BackRed      : 86
% 7.69/2.96  
% 7.69/2.96  #Partial instantiations: 0
% 7.69/2.96  #Strategies tried      : 1
% 7.69/2.96  
% 7.69/2.96  Timing (in seconds)
% 7.69/2.96  ----------------------
% 7.69/2.97  Preprocessing        : 0.54
% 7.69/2.97  Parsing              : 0.28
% 7.69/2.97  CNF conversion       : 0.04
% 7.69/2.97  Main loop            : 1.57
% 7.69/2.97  Inferencing          : 0.50
% 7.69/2.97  Reduction            : 0.43
% 7.69/2.97  Demodulation         : 0.28
% 7.69/2.97  BG Simplification    : 0.05
% 7.69/2.97  Subsumption          : 0.49
% 7.69/2.97  Abstraction          : 0.06
% 7.69/2.97  MUC search           : 0.00
% 7.69/2.97  Cooper               : 0.00
% 7.69/2.97  Total                : 2.19
% 7.69/2.97  Index Insertion      : 0.00
% 7.69/2.97  Index Deletion       : 0.00
% 7.69/2.97  Index Matching       : 0.00
% 7.69/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
