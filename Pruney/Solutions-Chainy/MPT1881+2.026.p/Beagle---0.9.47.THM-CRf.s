%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 403 expanded)
%              Number of leaves         :   41 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  322 (1187 expanded)
%              Number of equality atoms :   33 ( 114 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_180,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_162,axiom,(
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

tff(f_54,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_121,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16] : ~ v1_subset_1(k2_subset_1(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ! [A_16] : ~ v1_subset_1(A_16,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_1628,plain,(
    ! [B_266,A_267] :
      ( v2_tex_2(B_266,A_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267)
      | ~ v1_tdlat_3(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1649,plain,(
    ! [A_267] :
      ( v2_tex_2(u1_struct_0(A_267),A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v1_tdlat_3(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(resolution,[status(thm)],[c_75,c_1628])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_68,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_91,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_92,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_74])).

tff(c_93,plain,(
    ! [B_54,A_55] :
      ( v1_subset_1(B_54,A_55)
      | B_54 = A_55
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_96,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_58,c_93])).

tff(c_102,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_96])).

tff(c_169,plain,(
    ! [A_69,B_70] :
      ( k2_pre_topc(A_69,B_70) = B_70
      | ~ v4_pre_topc(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_179,plain,(
    ! [B_70] :
      ( k2_pre_topc('#skF_4',B_70) = B_70
      | ~ v4_pre_topc(B_70,'#skF_4')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_169])).

tff(c_189,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_4',B_71) = B_71
      | ~ v4_pre_topc(B_71,'#skF_4')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_179])).

tff(c_199,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_189])).

tff(c_200,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [B_72,A_73] :
      ( v3_pre_topc(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v1_tdlat_3(A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_211,plain,(
    ! [B_72] :
      ( v3_pre_topc(B_72,'#skF_4')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_5'))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_201])).

tff(c_221,plain,(
    ! [B_74] :
      ( v3_pre_topc(B_74,'#skF_4')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_62,c_211])).

tff(c_230,plain,(
    ! [B_4] :
      ( v3_pre_topc(k3_subset_1('#skF_5',B_4),'#skF_4')
      | ~ m1_subset_1(B_4,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_221])).

tff(c_392,plain,(
    ! [B_98,A_99] :
      ( v4_pre_topc(B_98,A_99)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_99),B_98),A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_398,plain,(
    ! [B_98] :
      ( v4_pre_topc(B_98,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1('#skF_5',B_98),'#skF_4')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_392])).

tff(c_402,plain,(
    ! [B_100] :
      ( v4_pre_topc(B_100,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1('#skF_5',B_100),'#skF_4')
      | ~ m1_subset_1(B_100,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_102,c_398])).

tff(c_407,plain,(
    ! [B_101] :
      ( v4_pre_topc(B_101,'#skF_4')
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_230,c_402])).

tff(c_415,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_407])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_415])).

tff(c_421,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_493,plain,(
    ! [B_112,A_113] :
      ( v1_tops_1(B_112,A_113)
      | k2_pre_topc(A_113,B_112) != u1_struct_0(A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_503,plain,(
    ! [B_112] :
      ( v1_tops_1(B_112,'#skF_4')
      | k2_pre_topc('#skF_4',B_112) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_112,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_493])).

tff(c_525,plain,(
    ! [B_115] :
      ( v1_tops_1(B_115,'#skF_4')
      | k2_pre_topc('#skF_4',B_115) != '#skF_5'
      | ~ m1_subset_1(B_115,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_102,c_503])).

tff(c_533,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_75,c_525])).

tff(c_537,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_533])).

tff(c_572,plain,(
    ! [B_123,A_124] :
      ( v2_tex_2(B_123,A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v1_tdlat_3(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_582,plain,(
    ! [B_123] :
      ( v2_tex_2(B_123,'#skF_4')
      | ~ m1_subset_1(B_123,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_572])).

tff(c_590,plain,(
    ! [B_123] :
      ( v2_tex_2(B_123,'#skF_4')
      | ~ m1_subset_1(B_123,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_582])).

tff(c_593,plain,(
    ! [B_125] :
      ( v2_tex_2(B_125,'#skF_4')
      | ~ m1_subset_1(B_125,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_590])).

tff(c_603,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_593])).

tff(c_1102,plain,(
    ! [B_186,A_187] :
      ( v3_tex_2(B_186,A_187)
      | ~ v2_tex_2(B_186,A_187)
      | ~ v1_tops_1(B_186,A_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1119,plain,(
    ! [B_186] :
      ( v3_tex_2(B_186,'#skF_4')
      | ~ v2_tex_2(B_186,'#skF_4')
      | ~ v1_tops_1(B_186,'#skF_4')
      | ~ m1_subset_1(B_186,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1102])).

tff(c_1129,plain,(
    ! [B_186] :
      ( v3_tex_2(B_186,'#skF_4')
      | ~ v2_tex_2(B_186,'#skF_4')
      | ~ v1_tops_1(B_186,'#skF_4')
      | ~ m1_subset_1(B_186,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1119])).

tff(c_1132,plain,(
    ! [B_188] :
      ( v3_tex_2(B_188,'#skF_4')
      | ~ v2_tex_2(B_188,'#skF_4')
      | ~ v1_tops_1(B_188,'#skF_4')
      | ~ m1_subset_1(B_188,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1129])).

tff(c_1147,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_1132])).

tff(c_1153,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_603,c_1147])).

tff(c_1155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1153])).

tff(c_1157,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1208,plain,(
    ! [A_203,B_204] :
      ( k2_pre_topc(A_203,B_204) = B_204
      | ~ v4_pre_topc(B_204,A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1218,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1208])).

tff(c_1227,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1218])).

tff(c_1229,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_1231,plain,(
    ! [B_206,A_207] :
      ( v3_pre_topc(B_206,A_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ v1_tdlat_3(A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1495,plain,(
    ! [A_249,B_250] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_249),B_250),A_249)
      | ~ v1_tdlat_3(A_249)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1231])).

tff(c_22,plain,(
    ! [B_22,A_20] :
      ( v4_pre_topc(B_22,A_20)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_20),B_22),A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1521,plain,(
    ! [B_253,A_254] :
      ( v4_pre_topc(B_253,A_254)
      | ~ v1_tdlat_3(A_254)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_254))) ) ),
    inference(resolution,[status(thm)],[c_1495,c_22])).

tff(c_1535,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1521])).

tff(c_1545,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_62,c_1535])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1229,c_1545])).

tff(c_1548,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_1576,plain,(
    ! [A_258,B_259] :
      ( k2_pre_topc(A_258,B_259) = u1_struct_0(A_258)
      | ~ v1_tops_1(B_259,A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1586,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1576])).

tff(c_1595,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1548,c_1586])).

tff(c_1597,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1595])).

tff(c_1598,plain,(
    ! [B_260,A_261] :
      ( v1_tops_1(B_260,A_261)
      | k2_pre_topc(A_261,B_260) != u1_struct_0(A_261)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1608,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1598])).

tff(c_1617,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1548,c_1608])).

tff(c_1618,plain,(
    u1_struct_0('#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1597,c_1617])).

tff(c_1697,plain,(
    ! [A_284,B_285,C_286] :
      ( r2_hidden('#skF_1'(A_284,B_285,C_286),B_285)
      | r1_tarski(B_285,C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(A_284))
      | ~ m1_subset_1(B_285,k1_zfmisc_1(A_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1995,plain,(
    ! [A_328,B_329,C_330,A_331] :
      ( r2_hidden('#skF_1'(A_328,B_329,C_330),A_331)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(A_331))
      | r1_tarski(B_329,C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(A_328))
      | ~ m1_subset_1(B_329,k1_zfmisc_1(A_328)) ) ),
    inference(resolution,[status(thm)],[c_1697,c_8])).

tff(c_10,plain,(
    ! [A_9,B_10,C_14] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10,C_14),C_14)
      | r1_tarski(B_10,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2004,plain,(
    ! [B_332,A_333,A_334] :
      ( ~ m1_subset_1(B_332,k1_zfmisc_1(A_333))
      | r1_tarski(B_332,A_333)
      | ~ m1_subset_1(A_333,k1_zfmisc_1(A_334))
      | ~ m1_subset_1(B_332,k1_zfmisc_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_1995,c_10])).

tff(c_2022,plain,(
    ! [A_334] :
      ( r1_tarski('#skF_5',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_334))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_58,c_2004])).

tff(c_2026,plain,(
    ! [A_335] :
      ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_335))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_335)) ) ),
    inference(splitLeft,[status(thm)],[c_2022])).

tff(c_2030,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_75,c_2026])).

tff(c_2034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2030])).

tff(c_2035,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2022])).

tff(c_44,plain,(
    ! [C_38,B_35,A_29] :
      ( C_38 = B_35
      | ~ r1_tarski(B_35,C_38)
      | ~ v2_tex_2(C_38,A_29)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ v3_tex_2(B_35,A_29)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2037,plain,(
    ! [A_29] :
      ( u1_struct_0('#skF_4') = '#skF_5'
      | ~ v2_tex_2(u1_struct_0('#skF_4'),A_29)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ v3_tex_2('#skF_5',A_29)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_2035,c_44])).

tff(c_2055,plain,(
    ! [A_341] :
      ( ~ v2_tex_2(u1_struct_0('#skF_4'),A_341)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ v3_tex_2('#skF_5',A_341)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1618,c_2037])).

tff(c_2059,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_2055])).

tff(c_2062,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1157,c_2059])).

tff(c_2070,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1649,c_2062])).

tff(c_2073,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2070])).

tff(c_2075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2073])).

tff(c_2076,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1595])).

tff(c_1156,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2078,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2076,c_1156])).

tff(c_2081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.73  
% 4.20/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.73  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 4.20/1.73  
% 4.20/1.73  %Foreground sorts:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Background operators:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Foreground operators:
% 4.20/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.20/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.20/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.73  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.20/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.20/1.73  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.20/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.73  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.20/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.73  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.20/1.73  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.20/1.73  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.20/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.73  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.20/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.20/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.20/1.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.20/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.73  
% 4.20/1.75  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.20/1.75  tff(f_57, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.20/1.75  tff(f_180, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.20/1.75  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.20/1.75  tff(f_146, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.20/1.75  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.20/1.75  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.20/1.75  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.20/1.75  tff(f_132, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.20/1.75  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 4.20/1.75  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.20/1.75  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.20/1.75  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 4.20/1.75  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.20/1.75  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.20/1.75  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.75  tff(c_16, plain, (![A_16]: (~v1_subset_1(k2_subset_1(A_16), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.20/1.75  tff(c_76, plain, (![A_16]: (~v1_subset_1(A_16, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 4.20/1.75  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_62, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.20/1.75  tff(c_75, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.20/1.75  tff(c_1628, plain, (![B_266, A_267]: (v2_tex_2(B_266, A_267) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267) | ~v1_tdlat_3(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.20/1.75  tff(c_1649, plain, (![A_267]: (v2_tex_2(u1_struct_0(A_267), A_267) | ~l1_pre_topc(A_267) | ~v1_tdlat_3(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(resolution, [status(thm)], [c_75, c_1628])).
% 4.20/1.75  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_68, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_91, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 4.20/1.75  tff(c_74, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.20/1.75  tff(c_92, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_74])).
% 4.20/1.75  tff(c_93, plain, (![B_54, A_55]: (v1_subset_1(B_54, A_55) | B_54=A_55 | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.75  tff(c_96, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_58, c_93])).
% 4.20/1.75  tff(c_102, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_92, c_96])).
% 4.20/1.75  tff(c_169, plain, (![A_69, B_70]: (k2_pre_topc(A_69, B_70)=B_70 | ~v4_pre_topc(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.75  tff(c_179, plain, (![B_70]: (k2_pre_topc('#skF_4', B_70)=B_70 | ~v4_pre_topc(B_70, '#skF_4') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_169])).
% 4.20/1.75  tff(c_189, plain, (![B_71]: (k2_pre_topc('#skF_4', B_71)=B_71 | ~v4_pre_topc(B_71, '#skF_4') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_179])).
% 4.20/1.75  tff(c_199, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_75, c_189])).
% 4.20/1.75  tff(c_200, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_199])).
% 4.20/1.75  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/1.75  tff(c_201, plain, (![B_72, A_73]: (v3_pre_topc(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~v1_tdlat_3(A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.20/1.75  tff(c_211, plain, (![B_72]: (v3_pre_topc(B_72, '#skF_4') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_5')) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_201])).
% 4.20/1.75  tff(c_221, plain, (![B_74]: (v3_pre_topc(B_74, '#skF_4') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_62, c_211])).
% 4.20/1.75  tff(c_230, plain, (![B_4]: (v3_pre_topc(k3_subset_1('#skF_5', B_4), '#skF_4') | ~m1_subset_1(B_4, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_221])).
% 4.20/1.75  tff(c_392, plain, (![B_98, A_99]: (v4_pre_topc(B_98, A_99) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_99), B_98), A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.20/1.75  tff(c_398, plain, (![B_98]: (v4_pre_topc(B_98, '#skF_4') | ~v3_pre_topc(k3_subset_1('#skF_5', B_98), '#skF_4') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_392])).
% 4.20/1.75  tff(c_402, plain, (![B_100]: (v4_pre_topc(B_100, '#skF_4') | ~v3_pre_topc(k3_subset_1('#skF_5', B_100), '#skF_4') | ~m1_subset_1(B_100, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_102, c_398])).
% 4.20/1.75  tff(c_407, plain, (![B_101]: (v4_pre_topc(B_101, '#skF_4') | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_230, c_402])).
% 4.20/1.75  tff(c_415, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_75, c_407])).
% 4.20/1.75  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_415])).
% 4.20/1.75  tff(c_421, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_199])).
% 4.20/1.75  tff(c_493, plain, (![B_112, A_113]: (v1_tops_1(B_112, A_113) | k2_pre_topc(A_113, B_112)!=u1_struct_0(A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.20/1.75  tff(c_503, plain, (![B_112]: (v1_tops_1(B_112, '#skF_4') | k2_pre_topc('#skF_4', B_112)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_112, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_493])).
% 4.20/1.75  tff(c_525, plain, (![B_115]: (v1_tops_1(B_115, '#skF_4') | k2_pre_topc('#skF_4', B_115)!='#skF_5' | ~m1_subset_1(B_115, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_102, c_503])).
% 4.20/1.75  tff(c_533, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_75, c_525])).
% 4.20/1.75  tff(c_537, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_533])).
% 4.20/1.75  tff(c_572, plain, (![B_123, A_124]: (v2_tex_2(B_123, A_124) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v1_tdlat_3(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.20/1.75  tff(c_582, plain, (![B_123]: (v2_tex_2(B_123, '#skF_4') | ~m1_subset_1(B_123, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_572])).
% 4.20/1.75  tff(c_590, plain, (![B_123]: (v2_tex_2(B_123, '#skF_4') | ~m1_subset_1(B_123, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_582])).
% 4.20/1.75  tff(c_593, plain, (![B_125]: (v2_tex_2(B_125, '#skF_4') | ~m1_subset_1(B_125, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_590])).
% 4.20/1.75  tff(c_603, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_75, c_593])).
% 4.20/1.75  tff(c_1102, plain, (![B_186, A_187]: (v3_tex_2(B_186, A_187) | ~v2_tex_2(B_186, A_187) | ~v1_tops_1(B_186, A_187) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.20/1.75  tff(c_1119, plain, (![B_186]: (v3_tex_2(B_186, '#skF_4') | ~v2_tex_2(B_186, '#skF_4') | ~v1_tops_1(B_186, '#skF_4') | ~m1_subset_1(B_186, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1102])).
% 4.20/1.75  tff(c_1129, plain, (![B_186]: (v3_tex_2(B_186, '#skF_4') | ~v2_tex_2(B_186, '#skF_4') | ~v1_tops_1(B_186, '#skF_4') | ~m1_subset_1(B_186, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1119])).
% 4.20/1.75  tff(c_1132, plain, (![B_188]: (v3_tex_2(B_188, '#skF_4') | ~v2_tex_2(B_188, '#skF_4') | ~v1_tops_1(B_188, '#skF_4') | ~m1_subset_1(B_188, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1129])).
% 4.20/1.75  tff(c_1147, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_75, c_1132])).
% 4.20/1.75  tff(c_1153, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_603, c_1147])).
% 4.20/1.75  tff(c_1155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_1153])).
% 4.20/1.75  tff(c_1157, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 4.20/1.75  tff(c_1208, plain, (![A_203, B_204]: (k2_pre_topc(A_203, B_204)=B_204 | ~v4_pre_topc(B_204, A_203) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.75  tff(c_1218, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1208])).
% 4.20/1.75  tff(c_1227, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1218])).
% 4.20/1.75  tff(c_1229, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1227])).
% 4.20/1.75  tff(c_1231, plain, (![B_206, A_207]: (v3_pre_topc(B_206, A_207) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~v1_tdlat_3(A_207) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.20/1.75  tff(c_1495, plain, (![A_249, B_250]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_249), B_250), A_249) | ~v1_tdlat_3(A_249) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))))), inference(resolution, [status(thm)], [c_6, c_1231])).
% 4.20/1.75  tff(c_22, plain, (![B_22, A_20]: (v4_pre_topc(B_22, A_20) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_20), B_22), A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.20/1.75  tff(c_1521, plain, (![B_253, A_254]: (v4_pre_topc(B_253, A_254) | ~v1_tdlat_3(A_254) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_254))))), inference(resolution, [status(thm)], [c_1495, c_22])).
% 4.20/1.75  tff(c_1535, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1521])).
% 4.20/1.75  tff(c_1545, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_62, c_1535])).
% 4.20/1.75  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1229, c_1545])).
% 4.20/1.75  tff(c_1548, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_1227])).
% 4.20/1.75  tff(c_1576, plain, (![A_258, B_259]: (k2_pre_topc(A_258, B_259)=u1_struct_0(A_258) | ~v1_tops_1(B_259, A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.20/1.75  tff(c_1586, plain, (k2_pre_topc('#skF_4', '#skF_5')=u1_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1576])).
% 4.20/1.75  tff(c_1595, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1548, c_1586])).
% 4.20/1.75  tff(c_1597, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1595])).
% 4.20/1.75  tff(c_1598, plain, (![B_260, A_261]: (v1_tops_1(B_260, A_261) | k2_pre_topc(A_261, B_260)!=u1_struct_0(A_261) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.20/1.75  tff(c_1608, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1598])).
% 4.20/1.75  tff(c_1617, plain, (v1_tops_1('#skF_5', '#skF_4') | u1_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1548, c_1608])).
% 4.20/1.75  tff(c_1618, plain, (u1_struct_0('#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1597, c_1617])).
% 4.20/1.75  tff(c_1697, plain, (![A_284, B_285, C_286]: (r2_hidden('#skF_1'(A_284, B_285, C_286), B_285) | r1_tarski(B_285, C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(A_284)) | ~m1_subset_1(B_285, k1_zfmisc_1(A_284)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.20/1.75  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.20/1.75  tff(c_1995, plain, (![A_328, B_329, C_330, A_331]: (r2_hidden('#skF_1'(A_328, B_329, C_330), A_331) | ~m1_subset_1(B_329, k1_zfmisc_1(A_331)) | r1_tarski(B_329, C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(A_328)) | ~m1_subset_1(B_329, k1_zfmisc_1(A_328)))), inference(resolution, [status(thm)], [c_1697, c_8])).
% 4.20/1.75  tff(c_10, plain, (![A_9, B_10, C_14]: (~r2_hidden('#skF_1'(A_9, B_10, C_14), C_14) | r1_tarski(B_10, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.20/1.75  tff(c_2004, plain, (![B_332, A_333, A_334]: (~m1_subset_1(B_332, k1_zfmisc_1(A_333)) | r1_tarski(B_332, A_333) | ~m1_subset_1(A_333, k1_zfmisc_1(A_334)) | ~m1_subset_1(B_332, k1_zfmisc_1(A_334)))), inference(resolution, [status(thm)], [c_1995, c_10])).
% 4.20/1.75  tff(c_2022, plain, (![A_334]: (r1_tarski('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_334)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_334)))), inference(resolution, [status(thm)], [c_58, c_2004])).
% 4.20/1.75  tff(c_2026, plain, (![A_335]: (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_335)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_335)))), inference(splitLeft, [status(thm)], [c_2022])).
% 4.20/1.75  tff(c_2030, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_75, c_2026])).
% 4.20/1.75  tff(c_2034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2030])).
% 4.20/1.75  tff(c_2035, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2022])).
% 4.20/1.75  tff(c_44, plain, (![C_38, B_35, A_29]: (C_38=B_35 | ~r1_tarski(B_35, C_38) | ~v2_tex_2(C_38, A_29) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_29))) | ~v3_tex_2(B_35, A_29) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.20/1.75  tff(c_2037, plain, (![A_29]: (u1_struct_0('#skF_4')='#skF_5' | ~v2_tex_2(u1_struct_0('#skF_4'), A_29) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_29))) | ~v3_tex_2('#skF_5', A_29) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_2035, c_44])).
% 4.20/1.75  tff(c_2055, plain, (![A_341]: (~v2_tex_2(u1_struct_0('#skF_4'), A_341) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_341))) | ~v3_tex_2('#skF_5', A_341) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(negUnitSimplification, [status(thm)], [c_1618, c_2037])).
% 4.20/1.75  tff(c_2059, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_75, c_2055])).
% 4.20/1.75  tff(c_2062, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1157, c_2059])).
% 4.20/1.75  tff(c_2070, plain, (~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1649, c_2062])).
% 4.20/1.75  tff(c_2073, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2070])).
% 4.20/1.75  tff(c_2075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2073])).
% 4.20/1.75  tff(c_2076, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1595])).
% 4.20/1.75  tff(c_1156, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 4.20/1.75  tff(c_2078, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2076, c_1156])).
% 4.20/1.75  tff(c_2081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2078])).
% 4.20/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.75  
% 4.20/1.75  Inference rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Ref     : 0
% 4.20/1.75  #Sup     : 386
% 4.20/1.75  #Fact    : 0
% 4.20/1.75  #Define  : 0
% 4.20/1.75  #Split   : 7
% 4.20/1.75  #Chain   : 0
% 4.20/1.75  #Close   : 0
% 4.20/1.75  
% 4.20/1.75  Ordering : KBO
% 4.20/1.75  
% 4.20/1.76  Simplification rules
% 4.20/1.76  ----------------------
% 4.20/1.76  #Subsume      : 32
% 4.20/1.76  #Demod        : 239
% 4.20/1.76  #Tautology    : 98
% 4.20/1.76  #SimpNegUnit  : 30
% 4.20/1.76  #BackRed      : 4
% 4.20/1.76  
% 4.20/1.76  #Partial instantiations: 0
% 4.20/1.76  #Strategies tried      : 1
% 4.20/1.76  
% 4.20/1.76  Timing (in seconds)
% 4.20/1.76  ----------------------
% 4.20/1.76  Preprocessing        : 0.34
% 4.20/1.76  Parsing              : 0.18
% 4.20/1.76  CNF conversion       : 0.02
% 4.20/1.76  Main loop            : 0.64
% 4.20/1.76  Inferencing          : 0.26
% 4.20/1.76  Reduction            : 0.17
% 4.20/1.76  Demodulation         : 0.12
% 4.20/1.76  BG Simplification    : 0.03
% 4.20/1.76  Subsumption          : 0.12
% 4.20/1.76  Abstraction          : 0.03
% 4.20/1.76  MUC search           : 0.00
% 4.20/1.76  Cooper               : 0.00
% 4.20/1.76  Total                : 1.03
% 4.20/1.76  Index Insertion      : 0.00
% 4.20/1.76  Index Deletion       : 0.00
% 4.20/1.76  Index Matching       : 0.00
% 4.20/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
