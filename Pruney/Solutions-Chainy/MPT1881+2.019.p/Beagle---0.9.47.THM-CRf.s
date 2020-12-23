%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:08 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  197 (1101 expanded)
%              Number of leaves         :   46 ( 390 expanded)
%              Depth                    :   14
%              Number of atoms          :  456 (2835 expanded)
%              Number of equality atoms :   49 ( 402 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_186,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_168,axiom,(
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

tff(f_127,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_15] : ~ v1_subset_1(k2_subset_1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_15] : ~ v1_subset_1(A_15,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_19] :
      ( m1_subset_1(k2_struct_0(A_19),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1625,plain,(
    ! [B_310,A_311] :
      ( v1_subset_1(B_310,A_311)
      | B_310 = A_311
      | ~ m1_subset_1(B_310,k1_zfmisc_1(A_311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1664,plain,(
    ! [A_322] :
      ( v1_subset_1(k2_struct_0(A_322),u1_struct_0(A_322))
      | u1_struct_0(A_322) = k2_struct_0(A_322)
      | ~ l1_struct_0(A_322) ) ),
    inference(resolution,[status(thm)],[c_22,c_1625])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_subset_1(k2_struct_0(A_21),u1_struct_0(A_21))
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1669,plain,(
    ! [A_323] :
      ( u1_struct_0(A_323) = k2_struct_0(A_323)
      | ~ l1_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_1664,c_26])).

tff(c_1679,plain,(
    ! [A_325] :
      ( u1_struct_0(A_325) = k2_struct_0(A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(resolution,[status(thm)],[c_24,c_1669])).

tff(c_1683,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1679])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1685,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_64])).

tff(c_80,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_97,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_74,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_100,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_74])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_110,plain,(
    ! [B_64,A_65] :
      ( v1_subset_1(B_64,A_65)
      | B_64 = A_65
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_116,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_64,c_110])).

tff(c_123,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_116])).

tff(c_389,plain,(
    ! [A_107,B_108] :
      ( k2_pre_topc(A_107,B_108) = B_108
      | ~ v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_399,plain,(
    ! [B_108] :
      ( k2_pre_topc('#skF_4',B_108) = B_108
      | ~ v4_pre_topc(B_108,'#skF_4')
      | ~ m1_subset_1(B_108,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_389])).

tff(c_413,plain,(
    ! [B_109] :
      ( k2_pre_topc('#skF_4',B_109) = B_109
      | ~ v4_pre_topc(B_109,'#skF_4')
      | ~ m1_subset_1(B_109,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_399])).

tff(c_423,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_413])).

tff(c_424,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k7_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_341,plain,(
    ! [B_100,A_101] :
      ( v3_pre_topc(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v1_tdlat_3(A_101)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_351,plain,(
    ! [B_100] :
      ( v3_pre_topc(B_100,'#skF_4')
      | ~ m1_subset_1(B_100,k1_zfmisc_1('#skF_5'))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_341])).

tff(c_365,plain,(
    ! [B_102] :
      ( v3_pre_topc(B_102,'#skF_4')
      | ~ m1_subset_1(B_102,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_351])).

tff(c_374,plain,(
    ! [B_9,C_10] :
      ( v3_pre_topc(k7_subset_1('#skF_5',B_9,C_10),'#skF_4')
      | ~ m1_subset_1(B_9,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_365])).

tff(c_137,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_4'),'#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_26])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_144])).

tff(c_149,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_150,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_134,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1('#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_22])).

tff(c_152,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_134])).

tff(c_38,plain,(
    ! [B_30,A_29] :
      ( v1_subset_1(B_30,A_29)
      | B_30 = A_29
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_155,plain,
    ( v1_subset_1(k2_struct_0('#skF_4'),'#skF_5')
    | k2_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_152,c_38])).

tff(c_158,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_155])).

tff(c_907,plain,(
    ! [B_193,A_194] :
      ( v4_pre_topc(B_193,A_194)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_194),k2_struct_0(A_194),B_193),A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_916,plain,(
    ! [B_193] :
      ( v4_pre_topc(B_193,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1('#skF_5',k2_struct_0('#skF_4'),B_193),'#skF_4')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_907])).

tff(c_922,plain,(
    ! [B_195] :
      ( v4_pre_topc(B_195,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1('#skF_5','#skF_5',B_195),'#skF_4')
      | ~ m1_subset_1(B_195,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123,c_158,c_916])).

tff(c_929,plain,(
    ! [C_10] :
      ( v4_pre_topc(C_10,'#skF_4')
      | ~ m1_subset_1(C_10,k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_374,c_922])).

tff(c_934,plain,(
    ! [C_196] :
      ( v4_pre_topc(C_196,'#skF_4')
      | ~ m1_subset_1(C_196,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_929])).

tff(c_942,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_934])).

tff(c_947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_942])).

tff(c_948,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_950,plain,(
    ! [B_197,A_198] :
      ( v1_tops_1(B_197,A_198)
      | k2_pre_topc(A_198,B_197) != u1_struct_0(A_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_960,plain,(
    ! [B_197] :
      ( v1_tops_1(B_197,'#skF_4')
      | k2_pre_topc('#skF_4',B_197) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_197,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_950])).

tff(c_978,plain,(
    ! [B_199] :
      ( v1_tops_1(B_199,'#skF_4')
      | k2_pre_topc('#skF_4',B_199) != '#skF_5'
      | ~ m1_subset_1(B_199,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123,c_960])).

tff(c_986,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_81,c_978])).

tff(c_990,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_986])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1112,plain,(
    ! [B_226,A_227] :
      ( v2_tex_2(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227)
      | ~ v1_tdlat_3(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1122,plain,(
    ! [B_226] :
      ( v2_tex_2(B_226,'#skF_4')
      | ~ m1_subset_1(B_226,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_1112])).

tff(c_1133,plain,(
    ! [B_226] :
      ( v2_tex_2(B_226,'#skF_4')
      | ~ m1_subset_1(B_226,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1122])).

tff(c_1137,plain,(
    ! [B_228] :
      ( v2_tex_2(B_228,'#skF_4')
      | ~ m1_subset_1(B_228,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1133])).

tff(c_1147,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_1137])).

tff(c_1558,plain,(
    ! [B_295,A_296] :
      ( v3_tex_2(B_295,A_296)
      | ~ v2_tex_2(B_295,A_296)
      | ~ v1_tops_1(B_295,A_296)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1568,plain,(
    ! [B_295] :
      ( v3_tex_2(B_295,'#skF_4')
      | ~ v2_tex_2(B_295,'#skF_4')
      | ~ v1_tops_1(B_295,'#skF_4')
      | ~ m1_subset_1(B_295,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_1558])).

tff(c_1579,plain,(
    ! [B_295] :
      ( v3_tex_2(B_295,'#skF_4')
      | ~ v2_tex_2(B_295,'#skF_4')
      | ~ v1_tops_1(B_295,'#skF_4')
      | ~ m1_subset_1(B_295,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1568])).

tff(c_1590,plain,(
    ! [B_298] :
      ( v3_tex_2(B_298,'#skF_4')
      | ~ v2_tex_2(B_298,'#skF_4')
      | ~ v1_tops_1(B_298,'#skF_4')
      | ~ m1_subset_1(B_298,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1579])).

tff(c_1598,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_1590])).

tff(c_1602,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_1147,c_1598])).

tff(c_1604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1602])).

tff(c_1605,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1747,plain,(
    ! [B_335,A_336] :
      ( v2_tex_2(B_335,A_336)
      | ~ v3_tex_2(B_335,A_336)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ l1_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1771,plain,(
    ! [A_337] :
      ( v2_tex_2(u1_struct_0(A_337),A_337)
      | ~ v3_tex_2(u1_struct_0(A_337),A_337)
      | ~ l1_pre_topc(A_337) ) ),
    inference(resolution,[status(thm)],[c_81,c_1747])).

tff(c_1774,plain,
    ( v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_1771])).

tff(c_1776,plain,
    ( v2_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1683,c_1774])).

tff(c_1777,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1776])).

tff(c_1802,plain,(
    ! [A_341,B_342] :
      ( k2_pre_topc(A_341,B_342) = B_342
      | ~ v4_pre_topc(B_342,A_341)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1826,plain,(
    ! [A_343] :
      ( k2_pre_topc(A_343,u1_struct_0(A_343)) = u1_struct_0(A_343)
      | ~ v4_pre_topc(u1_struct_0(A_343),A_343)
      | ~ l1_pre_topc(A_343) ) ),
    inference(resolution,[status(thm)],[c_81,c_1802])).

tff(c_1829,plain,
    ( k2_pre_topc('#skF_4',u1_struct_0('#skF_4')) = u1_struct_0('#skF_4')
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_1826])).

tff(c_1831,plain,
    ( k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4')
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1683,c_1683,c_1829])).

tff(c_1871,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1831])).

tff(c_1832,plain,(
    ! [B_344,A_345] :
      ( v3_pre_topc(B_344,A_345)
      | ~ m1_subset_1(B_344,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ v1_tdlat_3(A_345)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1835,plain,(
    ! [B_344] :
      ( v3_pre_topc(B_344,'#skF_4')
      | ~ m1_subset_1(B_344,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_1832])).

tff(c_1856,plain,(
    ! [B_346] :
      ( v3_pre_topc(B_346,'#skF_4')
      | ~ m1_subset_1(B_346,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_1835])).

tff(c_1869,plain,(
    ! [B_9,C_10] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),B_9,C_10),'#skF_4')
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1856])).

tff(c_3040,plain,(
    ! [B_510,A_511] :
      ( v4_pre_topc(B_510,A_511)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_511),k2_struct_0(A_511),B_510),A_511)
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ l1_pre_topc(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3043,plain,(
    ! [B_510] :
      ( v4_pre_topc(B_510,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_510),'#skF_4')
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_3040])).

tff(c_3069,plain,(
    ! [B_515] :
      ( v4_pre_topc(B_515,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_515),'#skF_4')
      | ~ m1_subset_1(B_515,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1683,c_3043])).

tff(c_3073,plain,(
    ! [C_10] :
      ( v4_pre_topc(C_10,'#skF_4')
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1869,c_3069])).

tff(c_3077,plain,(
    ! [C_516] :
      ( v4_pre_topc(C_516,'#skF_4')
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_3073])).

tff(c_3088,plain,(
    v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_3077])).

tff(c_3095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1871,c_3088])).

tff(c_3096,plain,(
    k2_pre_topc('#skF_4',k2_struct_0('#skF_4')) = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1831])).

tff(c_3109,plain,(
    ! [B_519,A_520] :
      ( v1_tops_1(B_519,A_520)
      | k2_pre_topc(A_520,B_519) != u1_struct_0(A_520)
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ l1_pre_topc(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3133,plain,(
    ! [A_521] :
      ( v1_tops_1(u1_struct_0(A_521),A_521)
      | k2_pre_topc(A_521,u1_struct_0(A_521)) != u1_struct_0(A_521)
      | ~ l1_pre_topc(A_521) ) ),
    inference(resolution,[status(thm)],[c_81,c_3109])).

tff(c_3136,plain,
    ( v1_tops_1(k2_struct_0('#skF_4'),'#skF_4')
    | k2_pre_topc('#skF_4',u1_struct_0('#skF_4')) != u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_3133])).

tff(c_3138,plain,(
    v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3096,c_1683,c_1683,c_3136])).

tff(c_3952,plain,(
    ! [B_641,A_642] :
      ( v2_tex_2(B_641,A_642)
      | ~ m1_subset_1(B_641,k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ l1_pre_topc(A_642)
      | ~ v1_tdlat_3(A_642)
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3955,plain,(
    ! [B_641] :
      ( v2_tex_2(B_641,'#skF_4')
      | ~ m1_subset_1(B_641,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_3952])).

tff(c_3971,plain,(
    ! [B_641] :
      ( v2_tex_2(B_641,'#skF_4')
      | ~ m1_subset_1(B_641,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3955])).

tff(c_3981,plain,(
    ! [B_644] :
      ( v2_tex_2(B_644,'#skF_4')
      | ~ m1_subset_1(B_644,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3971])).

tff(c_3996,plain,(
    v2_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_3981])).

tff(c_4999,plain,(
    ! [B_760,A_761] :
      ( v3_tex_2(B_760,A_761)
      | ~ v2_tex_2(B_760,A_761)
      | ~ v1_tops_1(B_760,A_761)
      | ~ m1_subset_1(B_760,k1_zfmisc_1(u1_struct_0(A_761)))
      | ~ l1_pre_topc(A_761)
      | ~ v2_pre_topc(A_761)
      | v2_struct_0(A_761) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_5005,plain,(
    ! [B_760] :
      ( v3_tex_2(B_760,'#skF_4')
      | ~ v2_tex_2(B_760,'#skF_4')
      | ~ v1_tops_1(B_760,'#skF_4')
      | ~ m1_subset_1(B_760,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_4999])).

tff(c_5022,plain,(
    ! [B_760] :
      ( v3_tex_2(B_760,'#skF_4')
      | ~ v2_tex_2(B_760,'#skF_4')
      | ~ v1_tops_1(B_760,'#skF_4')
      | ~ m1_subset_1(B_760,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_5005])).

tff(c_5028,plain,(
    ! [B_762] :
      ( v3_tex_2(B_762,'#skF_4')
      | ~ v2_tex_2(B_762,'#skF_4')
      | ~ v1_tops_1(B_762,'#skF_4')
      | ~ m1_subset_1(B_762,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5022])).

tff(c_5042,plain,
    ( v3_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v2_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v1_tops_1(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_5028])).

tff(c_5050,plain,(
    v3_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3138,c_3996,c_5042])).

tff(c_5052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1777,c_5050])).

tff(c_5053,plain,(
    v2_tex_2(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1776])).

tff(c_5087,plain,(
    ! [A_766,B_767] :
      ( k2_pre_topc(A_766,B_767) = B_767
      | ~ v4_pre_topc(B_767,A_766)
      | ~ m1_subset_1(B_767,k1_zfmisc_1(u1_struct_0(A_766)))
      | ~ l1_pre_topc(A_766) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5090,plain,(
    ! [B_767] :
      ( k2_pre_topc('#skF_4',B_767) = B_767
      | ~ v4_pre_topc(B_767,'#skF_4')
      | ~ m1_subset_1(B_767,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_5087])).

tff(c_6332,plain,(
    ! [B_940] :
      ( k2_pre_topc('#skF_4',B_940) = B_940
      | ~ v4_pre_topc(B_940,'#skF_4')
      | ~ m1_subset_1(B_940,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5090])).

tff(c_6344,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1685,c_6332])).

tff(c_6349,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6344])).

tff(c_5117,plain,(
    ! [B_769,A_770] :
      ( v3_pre_topc(B_769,A_770)
      | ~ m1_subset_1(B_769,k1_zfmisc_1(u1_struct_0(A_770)))
      | ~ v1_tdlat_3(A_770)
      | ~ l1_pre_topc(A_770)
      | ~ v2_pre_topc(A_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5120,plain,(
    ! [B_769] :
      ( v3_pre_topc(B_769,'#skF_4')
      | ~ m1_subset_1(B_769,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_5117])).

tff(c_5141,plain,(
    ! [B_771] :
      ( v3_pre_topc(B_771,'#skF_4')
      | ~ m1_subset_1(B_771,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_5120])).

tff(c_5154,plain,(
    ! [B_9,C_10] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),B_9,C_10),'#skF_4')
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_5141])).

tff(c_6818,plain,(
    ! [B_1010,A_1011] :
      ( v4_pre_topc(B_1010,A_1011)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_1011),k2_struct_0(A_1011),B_1010),A_1011)
      | ~ m1_subset_1(B_1010,k1_zfmisc_1(u1_struct_0(A_1011)))
      | ~ l1_pre_topc(A_1011) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6821,plain,(
    ! [B_1010] :
      ( v4_pre_topc(B_1010,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_1010),'#skF_4')
      | ~ m1_subset_1(B_1010,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_6818])).

tff(c_6851,plain,(
    ! [B_1016] :
      ( v4_pre_topc(B_1016,'#skF_4')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'),B_1016),'#skF_4')
      | ~ m1_subset_1(B_1016,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1683,c_6821])).

tff(c_6855,plain,(
    ! [C_10] :
      ( v4_pre_topc(C_10,'#skF_4')
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_5154,c_6851])).

tff(c_6859,plain,(
    ! [C_1017] :
      ( v4_pre_topc(C_1017,'#skF_4')
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_6855])).

tff(c_6862,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1685,c_6859])).

tff(c_6874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6349,c_6862])).

tff(c_6875,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6344])).

tff(c_6302,plain,(
    ! [B_937,A_938] :
      ( v1_tops_1(B_937,A_938)
      | k2_pre_topc(A_938,B_937) != u1_struct_0(A_938)
      | ~ m1_subset_1(B_937,k1_zfmisc_1(u1_struct_0(A_938)))
      | ~ l1_pre_topc(A_938) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6305,plain,(
    ! [B_937] :
      ( v1_tops_1(B_937,'#skF_4')
      | k2_pre_topc('#skF_4',B_937) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_937,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_6302])).

tff(c_6882,plain,(
    ! [B_1020] :
      ( v1_tops_1(B_1020,'#skF_4')
      | k2_pre_topc('#skF_4',B_1020) != k2_struct_0('#skF_4')
      | ~ m1_subset_1(B_1020,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1683,c_6305])).

tff(c_6885,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1685,c_6882])).

tff(c_6895,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6875,c_6885])).

tff(c_6924,plain,(
    k2_struct_0('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6895])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1642,plain,(
    ! [C_312,A_313,B_314] :
      ( r2_hidden(C_312,A_313)
      | ~ r2_hidden(C_312,B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(A_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1707,plain,(
    ! [A_326,B_327,A_328] :
      ( r2_hidden('#skF_1'(A_326,B_327),A_328)
      | ~ m1_subset_1(A_326,k1_zfmisc_1(A_328))
      | r1_tarski(A_326,B_327) ) ),
    inference(resolution,[status(thm)],[c_6,c_1642])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1719,plain,(
    ! [A_329,A_330] :
      ( ~ m1_subset_1(A_329,k1_zfmisc_1(A_330))
      | r1_tarski(A_329,A_330) ) ),
    inference(resolution,[status(thm)],[c_1707,c_4])).

tff(c_1735,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1685,c_1719])).

tff(c_8427,plain,(
    ! [C_1201,B_1202,A_1203] :
      ( C_1201 = B_1202
      | ~ r1_tarski(B_1202,C_1201)
      | ~ v2_tex_2(C_1201,A_1203)
      | ~ m1_subset_1(C_1201,k1_zfmisc_1(u1_struct_0(A_1203)))
      | ~ v3_tex_2(B_1202,A_1203)
      | ~ m1_subset_1(B_1202,k1_zfmisc_1(u1_struct_0(A_1203)))
      | ~ l1_pre_topc(A_1203) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8449,plain,(
    ! [A_1203] :
      ( k2_struct_0('#skF_4') = '#skF_5'
      | ~ v2_tex_2(k2_struct_0('#skF_4'),A_1203)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_1203)))
      | ~ v3_tex_2('#skF_5',A_1203)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_1203)))
      | ~ l1_pre_topc(A_1203) ) ),
    inference(resolution,[status(thm)],[c_1735,c_8427])).

tff(c_8881,plain,(
    ! [A_1252] :
      ( ~ v2_tex_2(k2_struct_0('#skF_4'),A_1252)
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_1252)))
      | ~ v3_tex_2('#skF_5',A_1252)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_1252)))
      | ~ l1_pre_topc(A_1252) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6924,c_8449])).

tff(c_8884,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_4'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_8881])).

tff(c_8891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1685,c_1683,c_1605,c_81,c_5053,c_8884])).

tff(c_8893,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6895])).

tff(c_1608,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1605,c_74])).

tff(c_1684,plain,(
    v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_1608])).

tff(c_8907,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8893,c_1684])).

tff(c_8918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_8907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/2.93  
% 7.96/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.96/2.93  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 7.96/2.93  
% 7.96/2.93  %Foreground sorts:
% 7.96/2.93  
% 7.96/2.93  
% 7.96/2.93  %Background operators:
% 7.96/2.93  
% 7.96/2.93  
% 7.96/2.93  %Foreground operators:
% 7.96/2.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.96/2.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.96/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.96/2.93  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.96/2.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.96/2.93  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.96/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.96/2.93  tff('#skF_5', type, '#skF_5': $i).
% 7.96/2.93  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.96/2.93  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.96/2.93  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.96/2.93  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.96/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.96/2.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.96/2.93  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.96/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/2.93  tff('#skF_4', type, '#skF_4': $i).
% 7.96/2.93  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.96/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/2.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.96/2.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.96/2.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.96/2.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.96/2.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.96/2.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.96/2.93  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.96/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.96/2.93  
% 8.02/2.96  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.02/2.96  tff(f_50, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 8.02/2.96  tff(f_186, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 8.02/2.96  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.02/2.96  tff(f_63, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 8.02/2.96  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 8.02/2.96  tff(f_72, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 8.02/2.96  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.02/2.96  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.02/2.96  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 8.02/2.96  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 8.02/2.96  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 8.02/2.96  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 8.02/2.96  tff(f_152, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 8.02/2.96  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 8.02/2.96  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 8.02/2.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.02/2.96  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.02/2.96  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.02/2.96  tff(c_16, plain, (![A_15]: (~v1_subset_1(k2_subset_1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.02/2.96  tff(c_82, plain, (![A_15]: (~v1_subset_1(A_15, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 8.02/2.96  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.02/2.96  tff(c_22, plain, (![A_19]: (m1_subset_1(k2_struct_0(A_19), k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.02/2.96  tff(c_1625, plain, (![B_310, A_311]: (v1_subset_1(B_310, A_311) | B_310=A_311 | ~m1_subset_1(B_310, k1_zfmisc_1(A_311)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.02/2.96  tff(c_1664, plain, (![A_322]: (v1_subset_1(k2_struct_0(A_322), u1_struct_0(A_322)) | u1_struct_0(A_322)=k2_struct_0(A_322) | ~l1_struct_0(A_322))), inference(resolution, [status(thm)], [c_22, c_1625])).
% 8.02/2.96  tff(c_26, plain, (![A_21]: (~v1_subset_1(k2_struct_0(A_21), u1_struct_0(A_21)) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.02/2.96  tff(c_1669, plain, (![A_323]: (u1_struct_0(A_323)=k2_struct_0(A_323) | ~l1_struct_0(A_323))), inference(resolution, [status(thm)], [c_1664, c_26])).
% 8.02/2.96  tff(c_1679, plain, (![A_325]: (u1_struct_0(A_325)=k2_struct_0(A_325) | ~l1_pre_topc(A_325))), inference(resolution, [status(thm)], [c_24, c_1669])).
% 8.02/2.96  tff(c_1683, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1679])).
% 8.02/2.96  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_1685, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_64])).
% 8.02/2.96  tff(c_80, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_97, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_80])).
% 8.02/2.96  tff(c_74, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_100, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_97, c_74])).
% 8.02/2.96  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.02/2.96  tff(c_81, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 8.02/2.96  tff(c_110, plain, (![B_64, A_65]: (v1_subset_1(B_64, A_65) | B_64=A_65 | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.02/2.96  tff(c_116, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_64, c_110])).
% 8.02/2.96  tff(c_123, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_97, c_116])).
% 8.02/2.96  tff(c_389, plain, (![A_107, B_108]: (k2_pre_topc(A_107, B_108)=B_108 | ~v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.02/2.96  tff(c_399, plain, (![B_108]: (k2_pre_topc('#skF_4', B_108)=B_108 | ~v4_pre_topc(B_108, '#skF_4') | ~m1_subset_1(B_108, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_389])).
% 8.02/2.96  tff(c_413, plain, (![B_109]: (k2_pre_topc('#skF_4', B_109)=B_109 | ~v4_pre_topc(B_109, '#skF_4') | ~m1_subset_1(B_109, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_399])).
% 8.02/2.96  tff(c_423, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_81, c_413])).
% 8.02/2.96  tff(c_424, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_423])).
% 8.02/2.96  tff(c_12, plain, (![A_8, B_9, C_10]: (m1_subset_1(k7_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.02/2.96  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_68, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_341, plain, (![B_100, A_101]: (v3_pre_topc(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~v1_tdlat_3(A_101) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.02/2.96  tff(c_351, plain, (![B_100]: (v3_pre_topc(B_100, '#skF_4') | ~m1_subset_1(B_100, k1_zfmisc_1('#skF_5')) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_341])).
% 8.02/2.96  tff(c_365, plain, (![B_102]: (v3_pre_topc(B_102, '#skF_4') | ~m1_subset_1(B_102, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_351])).
% 8.02/2.96  tff(c_374, plain, (![B_9, C_10]: (v3_pre_topc(k7_subset_1('#skF_5', B_9, C_10), '#skF_4') | ~m1_subset_1(B_9, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_365])).
% 8.02/2.96  tff(c_137, plain, (~v1_subset_1(k2_struct_0('#skF_4'), '#skF_5') | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_123, c_26])).
% 8.02/2.96  tff(c_141, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_137])).
% 8.02/2.96  tff(c_144, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_141])).
% 8.02/2.96  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_144])).
% 8.02/2.96  tff(c_149, plain, (~v1_subset_1(k2_struct_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_137])).
% 8.02/2.96  tff(c_150, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_137])).
% 8.02/2.96  tff(c_134, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1('#skF_5')) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_123, c_22])).
% 8.02/2.96  tff(c_152, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_134])).
% 8.02/2.96  tff(c_38, plain, (![B_30, A_29]: (v1_subset_1(B_30, A_29) | B_30=A_29 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.02/2.96  tff(c_155, plain, (v1_subset_1(k2_struct_0('#skF_4'), '#skF_5') | k2_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_152, c_38])).
% 8.02/2.96  tff(c_158, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_149, c_155])).
% 8.02/2.96  tff(c_907, plain, (![B_193, A_194]: (v4_pre_topc(B_193, A_194) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_194), k2_struct_0(A_194), B_193), A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.02/2.96  tff(c_916, plain, (![B_193]: (v4_pre_topc(B_193, '#skF_4') | ~v3_pre_topc(k7_subset_1('#skF_5', k2_struct_0('#skF_4'), B_193), '#skF_4') | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_907])).
% 8.02/2.96  tff(c_922, plain, (![B_195]: (v4_pre_topc(B_195, '#skF_4') | ~v3_pre_topc(k7_subset_1('#skF_5', '#skF_5', B_195), '#skF_4') | ~m1_subset_1(B_195, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_123, c_158, c_916])).
% 8.02/2.96  tff(c_929, plain, (![C_10]: (v4_pre_topc(C_10, '#skF_4') | ~m1_subset_1(C_10, k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_374, c_922])).
% 8.02/2.96  tff(c_934, plain, (![C_196]: (v4_pre_topc(C_196, '#skF_4') | ~m1_subset_1(C_196, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_929])).
% 8.02/2.96  tff(c_942, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_81, c_934])).
% 8.02/2.96  tff(c_947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_424, c_942])).
% 8.02/2.96  tff(c_948, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_423])).
% 8.02/2.96  tff(c_950, plain, (![B_197, A_198]: (v1_tops_1(B_197, A_198) | k2_pre_topc(A_198, B_197)!=u1_struct_0(A_198) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.02/2.96  tff(c_960, plain, (![B_197]: (v1_tops_1(B_197, '#skF_4') | k2_pre_topc('#skF_4', B_197)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_197, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_950])).
% 8.02/2.96  tff(c_978, plain, (![B_199]: (v1_tops_1(B_199, '#skF_4') | k2_pre_topc('#skF_4', B_199)!='#skF_5' | ~m1_subset_1(B_199, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_123, c_960])).
% 8.02/2.96  tff(c_986, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_81, c_978])).
% 8.02/2.96  tff(c_990, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_948, c_986])).
% 8.02/2.96  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 8.02/2.96  tff(c_1112, plain, (![B_226, A_227]: (v2_tex_2(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227) | ~v1_tdlat_3(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.02/2.96  tff(c_1122, plain, (![B_226]: (v2_tex_2(B_226, '#skF_4') | ~m1_subset_1(B_226, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_1112])).
% 8.02/2.96  tff(c_1133, plain, (![B_226]: (v2_tex_2(B_226, '#skF_4') | ~m1_subset_1(B_226, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1122])).
% 8.02/2.96  tff(c_1137, plain, (![B_228]: (v2_tex_2(B_228, '#skF_4') | ~m1_subset_1(B_228, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1133])).
% 8.02/2.96  tff(c_1147, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_81, c_1137])).
% 8.02/2.96  tff(c_1558, plain, (![B_295, A_296]: (v3_tex_2(B_295, A_296) | ~v2_tex_2(B_295, A_296) | ~v1_tops_1(B_295, A_296) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.02/2.96  tff(c_1568, plain, (![B_295]: (v3_tex_2(B_295, '#skF_4') | ~v2_tex_2(B_295, '#skF_4') | ~v1_tops_1(B_295, '#skF_4') | ~m1_subset_1(B_295, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_1558])).
% 8.02/2.96  tff(c_1579, plain, (![B_295]: (v3_tex_2(B_295, '#skF_4') | ~v2_tex_2(B_295, '#skF_4') | ~v1_tops_1(B_295, '#skF_4') | ~m1_subset_1(B_295, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1568])).
% 8.02/2.96  tff(c_1590, plain, (![B_298]: (v3_tex_2(B_298, '#skF_4') | ~v2_tex_2(B_298, '#skF_4') | ~v1_tops_1(B_298, '#skF_4') | ~m1_subset_1(B_298, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1579])).
% 8.02/2.96  tff(c_1598, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_81, c_1590])).
% 8.02/2.96  tff(c_1602, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_990, c_1147, c_1598])).
% 8.02/2.96  tff(c_1604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1602])).
% 8.02/2.96  tff(c_1605, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 8.02/2.96  tff(c_1747, plain, (![B_335, A_336]: (v2_tex_2(B_335, A_336) | ~v3_tex_2(B_335, A_336) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_336))) | ~l1_pre_topc(A_336))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.02/2.96  tff(c_1771, plain, (![A_337]: (v2_tex_2(u1_struct_0(A_337), A_337) | ~v3_tex_2(u1_struct_0(A_337), A_337) | ~l1_pre_topc(A_337))), inference(resolution, [status(thm)], [c_81, c_1747])).
% 8.02/2.96  tff(c_1774, plain, (v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1683, c_1771])).
% 8.02/2.96  tff(c_1776, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1683, c_1774])).
% 8.02/2.96  tff(c_1777, plain, (~v3_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1776])).
% 8.02/2.96  tff(c_1802, plain, (![A_341, B_342]: (k2_pre_topc(A_341, B_342)=B_342 | ~v4_pre_topc(B_342, A_341) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.02/2.96  tff(c_1826, plain, (![A_343]: (k2_pre_topc(A_343, u1_struct_0(A_343))=u1_struct_0(A_343) | ~v4_pre_topc(u1_struct_0(A_343), A_343) | ~l1_pre_topc(A_343))), inference(resolution, [status(thm)], [c_81, c_1802])).
% 8.02/2.96  tff(c_1829, plain, (k2_pre_topc('#skF_4', u1_struct_0('#skF_4'))=u1_struct_0('#skF_4') | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1683, c_1826])).
% 8.02/2.96  tff(c_1831, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4') | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1683, c_1683, c_1829])).
% 8.02/2.96  tff(c_1871, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1831])).
% 8.02/2.96  tff(c_1832, plain, (![B_344, A_345]: (v3_pre_topc(B_344, A_345) | ~m1_subset_1(B_344, k1_zfmisc_1(u1_struct_0(A_345))) | ~v1_tdlat_3(A_345) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.02/2.96  tff(c_1835, plain, (![B_344]: (v3_pre_topc(B_344, '#skF_4') | ~m1_subset_1(B_344, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_1832])).
% 8.02/2.96  tff(c_1856, plain, (![B_346]: (v3_pre_topc(B_346, '#skF_4') | ~m1_subset_1(B_346, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_1835])).
% 8.02/2.96  tff(c_1869, plain, (![B_9, C_10]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), B_9, C_10), '#skF_4') | ~m1_subset_1(B_9, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_12, c_1856])).
% 8.02/2.96  tff(c_3040, plain, (![B_510, A_511]: (v4_pre_topc(B_510, A_511) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_511), k2_struct_0(A_511), B_510), A_511) | ~m1_subset_1(B_510, k1_zfmisc_1(u1_struct_0(A_511))) | ~l1_pre_topc(A_511))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.02/2.96  tff(c_3043, plain, (![B_510]: (v4_pre_topc(B_510, '#skF_4') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_510), '#skF_4') | ~m1_subset_1(B_510, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_3040])).
% 8.02/2.96  tff(c_3069, plain, (![B_515]: (v4_pre_topc(B_515, '#skF_4') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_515), '#skF_4') | ~m1_subset_1(B_515, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1683, c_3043])).
% 8.02/2.96  tff(c_3073, plain, (![C_10]: (v4_pre_topc(C_10, '#skF_4') | ~m1_subset_1(C_10, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1869, c_3069])).
% 8.02/2.96  tff(c_3077, plain, (![C_516]: (v4_pre_topc(C_516, '#skF_4') | ~m1_subset_1(C_516, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_3073])).
% 8.02/2.96  tff(c_3088, plain, (v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_81, c_3077])).
% 8.02/2.96  tff(c_3095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1871, c_3088])).
% 8.02/2.96  tff(c_3096, plain, (k2_pre_topc('#skF_4', k2_struct_0('#skF_4'))=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1831])).
% 8.02/2.96  tff(c_3109, plain, (![B_519, A_520]: (v1_tops_1(B_519, A_520) | k2_pre_topc(A_520, B_519)!=u1_struct_0(A_520) | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0(A_520))) | ~l1_pre_topc(A_520))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.02/2.96  tff(c_3133, plain, (![A_521]: (v1_tops_1(u1_struct_0(A_521), A_521) | k2_pre_topc(A_521, u1_struct_0(A_521))!=u1_struct_0(A_521) | ~l1_pre_topc(A_521))), inference(resolution, [status(thm)], [c_81, c_3109])).
% 8.02/2.96  tff(c_3136, plain, (v1_tops_1(k2_struct_0('#skF_4'), '#skF_4') | k2_pre_topc('#skF_4', u1_struct_0('#skF_4'))!=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1683, c_3133])).
% 8.02/2.96  tff(c_3138, plain, (v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3096, c_1683, c_1683, c_3136])).
% 8.02/2.96  tff(c_3952, plain, (![B_641, A_642]: (v2_tex_2(B_641, A_642) | ~m1_subset_1(B_641, k1_zfmisc_1(u1_struct_0(A_642))) | ~l1_pre_topc(A_642) | ~v1_tdlat_3(A_642) | ~v2_pre_topc(A_642) | v2_struct_0(A_642))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.02/2.96  tff(c_3955, plain, (![B_641]: (v2_tex_2(B_641, '#skF_4') | ~m1_subset_1(B_641, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_3952])).
% 8.02/2.96  tff(c_3971, plain, (![B_641]: (v2_tex_2(B_641, '#skF_4') | ~m1_subset_1(B_641, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3955])).
% 8.02/2.96  tff(c_3981, plain, (![B_644]: (v2_tex_2(B_644, '#skF_4') | ~m1_subset_1(B_644, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_3971])).
% 8.02/2.96  tff(c_3996, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_81, c_3981])).
% 8.02/2.96  tff(c_4999, plain, (![B_760, A_761]: (v3_tex_2(B_760, A_761) | ~v2_tex_2(B_760, A_761) | ~v1_tops_1(B_760, A_761) | ~m1_subset_1(B_760, k1_zfmisc_1(u1_struct_0(A_761))) | ~l1_pre_topc(A_761) | ~v2_pre_topc(A_761) | v2_struct_0(A_761))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.02/2.96  tff(c_5005, plain, (![B_760]: (v3_tex_2(B_760, '#skF_4') | ~v2_tex_2(B_760, '#skF_4') | ~v1_tops_1(B_760, '#skF_4') | ~m1_subset_1(B_760, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_4999])).
% 8.02/2.96  tff(c_5022, plain, (![B_760]: (v3_tex_2(B_760, '#skF_4') | ~v2_tex_2(B_760, '#skF_4') | ~v1_tops_1(B_760, '#skF_4') | ~m1_subset_1(B_760, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_5005])).
% 8.02/2.96  tff(c_5028, plain, (![B_762]: (v3_tex_2(B_762, '#skF_4') | ~v2_tex_2(B_762, '#skF_4') | ~v1_tops_1(B_762, '#skF_4') | ~m1_subset_1(B_762, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_5022])).
% 8.02/2.96  tff(c_5042, plain, (v3_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~v2_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~v1_tops_1(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_81, c_5028])).
% 8.02/2.96  tff(c_5050, plain, (v3_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3138, c_3996, c_5042])).
% 8.02/2.96  tff(c_5052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1777, c_5050])).
% 8.02/2.96  tff(c_5053, plain, (v2_tex_2(k2_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_1776])).
% 8.02/2.96  tff(c_5087, plain, (![A_766, B_767]: (k2_pre_topc(A_766, B_767)=B_767 | ~v4_pre_topc(B_767, A_766) | ~m1_subset_1(B_767, k1_zfmisc_1(u1_struct_0(A_766))) | ~l1_pre_topc(A_766))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.02/2.96  tff(c_5090, plain, (![B_767]: (k2_pre_topc('#skF_4', B_767)=B_767 | ~v4_pre_topc(B_767, '#skF_4') | ~m1_subset_1(B_767, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_5087])).
% 8.02/2.96  tff(c_6332, plain, (![B_940]: (k2_pre_topc('#skF_4', B_940)=B_940 | ~v4_pre_topc(B_940, '#skF_4') | ~m1_subset_1(B_940, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5090])).
% 8.02/2.96  tff(c_6344, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1685, c_6332])).
% 8.02/2.96  tff(c_6349, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_6344])).
% 8.02/2.96  tff(c_5117, plain, (![B_769, A_770]: (v3_pre_topc(B_769, A_770) | ~m1_subset_1(B_769, k1_zfmisc_1(u1_struct_0(A_770))) | ~v1_tdlat_3(A_770) | ~l1_pre_topc(A_770) | ~v2_pre_topc(A_770))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.02/2.96  tff(c_5120, plain, (![B_769]: (v3_pre_topc(B_769, '#skF_4') | ~m1_subset_1(B_769, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_5117])).
% 8.02/2.96  tff(c_5141, plain, (![B_771]: (v3_pre_topc(B_771, '#skF_4') | ~m1_subset_1(B_771, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_5120])).
% 8.02/2.96  tff(c_5154, plain, (![B_9, C_10]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), B_9, C_10), '#skF_4') | ~m1_subset_1(B_9, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_12, c_5141])).
% 8.02/2.96  tff(c_6818, plain, (![B_1010, A_1011]: (v4_pre_topc(B_1010, A_1011) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_1011), k2_struct_0(A_1011), B_1010), A_1011) | ~m1_subset_1(B_1010, k1_zfmisc_1(u1_struct_0(A_1011))) | ~l1_pre_topc(A_1011))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.02/2.96  tff(c_6821, plain, (![B_1010]: (v4_pre_topc(B_1010, '#skF_4') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_1010), '#skF_4') | ~m1_subset_1(B_1010, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_6818])).
% 8.02/2.96  tff(c_6851, plain, (![B_1016]: (v4_pre_topc(B_1016, '#skF_4') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'), B_1016), '#skF_4') | ~m1_subset_1(B_1016, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1683, c_6821])).
% 8.02/2.96  tff(c_6855, plain, (![C_10]: (v4_pre_topc(C_10, '#skF_4') | ~m1_subset_1(C_10, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_5154, c_6851])).
% 8.02/2.96  tff(c_6859, plain, (![C_1017]: (v4_pre_topc(C_1017, '#skF_4') | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_6855])).
% 8.02/2.96  tff(c_6862, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1685, c_6859])).
% 8.02/2.96  tff(c_6874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6349, c_6862])).
% 8.02/2.96  tff(c_6875, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_6344])).
% 8.02/2.96  tff(c_6302, plain, (![B_937, A_938]: (v1_tops_1(B_937, A_938) | k2_pre_topc(A_938, B_937)!=u1_struct_0(A_938) | ~m1_subset_1(B_937, k1_zfmisc_1(u1_struct_0(A_938))) | ~l1_pre_topc(A_938))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.02/2.96  tff(c_6305, plain, (![B_937]: (v1_tops_1(B_937, '#skF_4') | k2_pre_topc('#skF_4', B_937)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_937, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1683, c_6302])).
% 8.02/2.96  tff(c_6882, plain, (![B_1020]: (v1_tops_1(B_1020, '#skF_4') | k2_pre_topc('#skF_4', B_1020)!=k2_struct_0('#skF_4') | ~m1_subset_1(B_1020, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1683, c_6305])).
% 8.02/2.96  tff(c_6885, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1685, c_6882])).
% 8.02/2.96  tff(c_6895, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6875, c_6885])).
% 8.02/2.96  tff(c_6924, plain, (k2_struct_0('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_6895])).
% 8.02/2.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.02/2.96  tff(c_1642, plain, (![C_312, A_313, B_314]: (r2_hidden(C_312, A_313) | ~r2_hidden(C_312, B_314) | ~m1_subset_1(B_314, k1_zfmisc_1(A_313)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.02/2.96  tff(c_1707, plain, (![A_326, B_327, A_328]: (r2_hidden('#skF_1'(A_326, B_327), A_328) | ~m1_subset_1(A_326, k1_zfmisc_1(A_328)) | r1_tarski(A_326, B_327))), inference(resolution, [status(thm)], [c_6, c_1642])).
% 8.02/2.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.02/2.96  tff(c_1719, plain, (![A_329, A_330]: (~m1_subset_1(A_329, k1_zfmisc_1(A_330)) | r1_tarski(A_329, A_330))), inference(resolution, [status(thm)], [c_1707, c_4])).
% 8.02/2.96  tff(c_1735, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1685, c_1719])).
% 8.02/2.96  tff(c_8427, plain, (![C_1201, B_1202, A_1203]: (C_1201=B_1202 | ~r1_tarski(B_1202, C_1201) | ~v2_tex_2(C_1201, A_1203) | ~m1_subset_1(C_1201, k1_zfmisc_1(u1_struct_0(A_1203))) | ~v3_tex_2(B_1202, A_1203) | ~m1_subset_1(B_1202, k1_zfmisc_1(u1_struct_0(A_1203))) | ~l1_pre_topc(A_1203))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.02/2.96  tff(c_8449, plain, (![A_1203]: (k2_struct_0('#skF_4')='#skF_5' | ~v2_tex_2(k2_struct_0('#skF_4'), A_1203) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_1203))) | ~v3_tex_2('#skF_5', A_1203) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_1203))) | ~l1_pre_topc(A_1203))), inference(resolution, [status(thm)], [c_1735, c_8427])).
% 8.02/2.96  tff(c_8881, plain, (![A_1252]: (~v2_tex_2(k2_struct_0('#skF_4'), A_1252) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_1252))) | ~v3_tex_2('#skF_5', A_1252) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_1252))) | ~l1_pre_topc(A_1252))), inference(negUnitSimplification, [status(thm)], [c_6924, c_8449])).
% 8.02/2.96  tff(c_8884, plain, (~v2_tex_2(k2_struct_0('#skF_4'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1683, c_8881])).
% 8.02/2.96  tff(c_8891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1685, c_1683, c_1605, c_81, c_5053, c_8884])).
% 8.02/2.96  tff(c_8893, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_6895])).
% 8.02/2.96  tff(c_1608, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1605, c_74])).
% 8.02/2.96  tff(c_1684, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_1608])).
% 8.02/2.96  tff(c_8907, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8893, c_1684])).
% 8.02/2.96  tff(c_8918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_8907])).
% 8.02/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/2.96  
% 8.02/2.96  Inference rules
% 8.02/2.96  ----------------------
% 8.02/2.96  #Ref     : 0
% 8.02/2.96  #Sup     : 1942
% 8.02/2.96  #Fact    : 0
% 8.02/2.96  #Define  : 0
% 8.02/2.96  #Split   : 34
% 8.02/2.96  #Chain   : 0
% 8.02/2.96  #Close   : 0
% 8.02/2.96  
% 8.02/2.96  Ordering : KBO
% 8.02/2.96  
% 8.02/2.96  Simplification rules
% 8.02/2.96  ----------------------
% 8.02/2.96  #Subsume      : 466
% 8.02/2.96  #Demod        : 1072
% 8.02/2.96  #Tautology    : 312
% 8.02/2.96  #SimpNegUnit  : 105
% 8.02/2.96  #BackRed      : 21
% 8.02/2.96  
% 8.02/2.96  #Partial instantiations: 0
% 8.02/2.96  #Strategies tried      : 1
% 8.02/2.96  
% 8.02/2.96  Timing (in seconds)
% 8.02/2.96  ----------------------
% 8.02/2.96  Preprocessing        : 0.40
% 8.02/2.96  Parsing              : 0.21
% 8.02/2.96  CNF conversion       : 0.03
% 8.02/2.96  Main loop            : 1.78
% 8.02/2.96  Inferencing          : 0.60
% 8.02/2.96  Reduction            : 0.51
% 8.02/2.96  Demodulation         : 0.32
% 8.02/2.96  BG Simplification    : 0.06
% 8.02/2.96  Subsumption          : 0.47
% 8.02/2.96  Abstraction          : 0.07
% 8.02/2.96  MUC search           : 0.00
% 8.02/2.96  Cooper               : 0.00
% 8.02/2.96  Total                : 2.24
% 8.02/2.96  Index Insertion      : 0.00
% 8.02/2.97  Index Deletion       : 0.00
% 8.02/2.97  Index Matching       : 0.00
% 8.02/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
