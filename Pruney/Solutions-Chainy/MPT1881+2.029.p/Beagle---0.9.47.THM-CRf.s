%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:10 EST 2020

% Result     : Theorem 9.68s
% Output     : CNFRefutation 9.89s
% Verified   : 
% Statistics : Number of formulae       :  192 (1216 expanded)
%              Number of leaves         :   40 ( 430 expanded)
%              Depth                    :   14
%              Number of atoms          :  456 (3154 expanded)
%              Number of equality atoms :   75 ( 501 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_163,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_145,axiom,(
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

tff(f_115,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_617,plain,(
    ! [A_136] :
      ( u1_struct_0(A_136) = k2_struct_0(A_136)
      | ~ l1_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_623,plain,(
    ! [A_138] :
      ( u1_struct_0(A_138) = k2_struct_0(A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_18,c_617])).

tff(c_627,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_623])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_629,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_52])).

tff(c_62,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_83,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_84,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_94,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_90])).

tff(c_68,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_100,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68])).

tff(c_101,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_100])).

tff(c_95,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_52])).

tff(c_115,plain,(
    ! [B_58,A_59] :
      ( v1_subset_1(B_58,A_59)
      | B_58 = A_59
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_118,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_95,c_115])).

tff(c_124,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_118])).

tff(c_20,plain,(
    ! [A_15] :
      ( v4_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_20])).

tff(c_140,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_136])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_94])).

tff(c_203,plain,(
    ! [A_75,B_76] :
      ( k2_pre_topc(A_75,B_76) = B_76
      | ~ v4_pre_topc(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [B_76] :
      ( k2_pre_topc('#skF_3',B_76) = B_76
      | ~ v4_pre_topc(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_203])).

tff(c_214,plain,(
    ! [B_77] :
      ( k2_pre_topc('#skF_3',B_77) = B_77
      | ~ v4_pre_topc(B_77,'#skF_3')
      | ~ m1_subset_1(B_77,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_206])).

tff(c_218,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_214])).

tff(c_221,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_218])).

tff(c_250,plain,(
    ! [B_82,A_83] :
      ( v1_tops_1(B_82,A_83)
      | k2_pre_topc(A_83,B_82) != k2_struct_0(A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_253,plain,(
    ! [B_82] :
      ( v1_tops_1(B_82,'#skF_3')
      | k2_pre_topc('#skF_3',B_82) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_250])).

tff(c_261,plain,(
    ! [B_84] :
      ( v1_tops_1(B_84,'#skF_3')
      | k2_pre_topc('#skF_3',B_84) != '#skF_4'
      | ~ m1_subset_1(B_84,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_124,c_253])).

tff(c_265,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_261])).

tff(c_268,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_265])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_322,plain,(
    ! [B_99,A_100] :
      ( v2_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v1_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_325,plain,(
    ! [B_99] :
      ( v2_tex_2(B_99,'#skF_3')
      | ~ m1_subset_1(B_99,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_322])).

tff(c_331,plain,(
    ! [B_99] :
      ( v2_tex_2(B_99,'#skF_3')
      | ~ m1_subset_1(B_99,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_325])).

tff(c_334,plain,(
    ! [B_101] :
      ( v2_tex_2(B_101,'#skF_3')
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_331])).

tff(c_339,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_334])).

tff(c_583,plain,(
    ! [B_133,A_134] :
      ( v3_tex_2(B_133,A_134)
      | ~ v2_tex_2(B_133,A_134)
      | ~ v1_tops_1(B_133,A_134)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_589,plain,(
    ! [B_133] :
      ( v3_tex_2(B_133,'#skF_3')
      | ~ v2_tex_2(B_133,'#skF_3')
      | ~ v1_tops_1(B_133,'#skF_3')
      | ~ m1_subset_1(B_133,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_583])).

tff(c_596,plain,(
    ! [B_133] :
      ( v3_tex_2(B_133,'#skF_3')
      | ~ v2_tex_2(B_133,'#skF_3')
      | ~ v1_tops_1(B_133,'#skF_3')
      | ~ m1_subset_1(B_133,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_589])).

tff(c_599,plain,(
    ! [B_135] :
      ( v3_tex_2(B_135,'#skF_3')
      | ~ v2_tex_2(B_135,'#skF_3')
      | ~ v1_tops_1(B_135,'#skF_3')
      | ~ m1_subset_1(B_135,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_596])).

tff(c_606,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_599])).

tff(c_610,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_339,c_606])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_610])).

tff(c_614,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_688,plain,(
    ! [B_159,A_160] :
      ( v2_tex_2(B_159,A_160)
      | ~ v3_tex_2(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_709,plain,(
    ! [A_163] :
      ( v2_tex_2(u1_struct_0(A_163),A_163)
      | ~ v3_tex_2(u1_struct_0(A_163),A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_70,c_688])).

tff(c_712,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_709])).

tff(c_714,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_627,c_712])).

tff(c_715,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_728,plain,(
    ! [A_165,B_166] :
      ( k2_pre_topc(A_165,B_166) = B_166
      | ~ v4_pre_topc(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_739,plain,(
    ! [A_167] :
      ( k2_pre_topc(A_167,u1_struct_0(A_167)) = u1_struct_0(A_167)
      | ~ v4_pre_topc(u1_struct_0(A_167),A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_70,c_728])).

tff(c_742,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_739])).

tff(c_744,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_627,c_627,c_742])).

tff(c_756,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_744])).

tff(c_759,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_756])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_759])).

tff(c_764,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_790,plain,(
    ! [B_172,A_173] :
      ( v1_tops_1(B_172,A_173)
      | k2_pre_topc(A_173,B_172) != k2_struct_0(A_173)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_801,plain,(
    ! [A_174] :
      ( v1_tops_1(u1_struct_0(A_174),A_174)
      | k2_pre_topc(A_174,u1_struct_0(A_174)) != k2_struct_0(A_174)
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_70,c_790])).

tff(c_807,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_801])).

tff(c_810,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_764,c_627,c_807])).

tff(c_857,plain,(
    ! [B_183,A_184] :
      ( v2_tex_2(B_183,A_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ v1_tdlat_3(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_860,plain,(
    ! [B_183] :
      ( v2_tex_2(B_183,'#skF_3')
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_857])).

tff(c_866,plain,(
    ! [B_183] :
      ( v2_tex_2(B_183,'#skF_3')
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_860])).

tff(c_873,plain,(
    ! [B_186] :
      ( v2_tex_2(B_186,'#skF_3')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_866])).

tff(c_883,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_873])).

tff(c_1425,plain,(
    ! [B_267,A_268] :
      ( v3_tex_2(B_267,A_268)
      | ~ v2_tex_2(B_267,A_268)
      | ~ v1_tops_1(B_267,A_268)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1428,plain,(
    ! [B_267] :
      ( v3_tex_2(B_267,'#skF_3')
      | ~ v2_tex_2(B_267,'#skF_3')
      | ~ v1_tops_1(B_267,'#skF_3')
      | ~ m1_subset_1(B_267,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1425])).

tff(c_1434,plain,(
    ! [B_267] :
      ( v3_tex_2(B_267,'#skF_3')
      | ~ v2_tex_2(B_267,'#skF_3')
      | ~ v1_tops_1(B_267,'#skF_3')
      | ~ m1_subset_1(B_267,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1428])).

tff(c_1437,plain,(
    ! [B_269] :
      ( v3_tex_2(B_269,'#skF_3')
      | ~ v2_tex_2(B_269,'#skF_3')
      | ~ v1_tops_1(B_269,'#skF_3')
      | ~ m1_subset_1(B_269,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1434])).

tff(c_1444,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1437])).

tff(c_1450,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_883,c_1444])).

tff(c_1452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_715,c_1450])).

tff(c_1453,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_1469,plain,(
    ! [A_271,B_272] :
      ( k2_pre_topc(A_271,B_272) = B_272
      | ~ v4_pre_topc(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1472,plain,(
    ! [B_272] :
      ( k2_pre_topc('#skF_3',B_272) = B_272
      | ~ v4_pre_topc(B_272,'#skF_3')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1469])).

tff(c_1517,plain,(
    ! [B_277] :
      ( k2_pre_topc('#skF_3',B_277) = B_277
      | ~ v4_pre_topc(B_277,'#skF_3')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1472])).

tff(c_1525,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_629,c_1517])).

tff(c_1529,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1525])).

tff(c_1496,plain,(
    ! [A_274,B_275] :
      ( k2_pre_topc(A_274,B_275) = k2_struct_0(A_274)
      | ~ v1_tops_1(B_275,A_274)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1499,plain,(
    ! [B_275] :
      ( k2_pre_topc('#skF_3',B_275) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_275,'#skF_3')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1496])).

tff(c_1530,plain,(
    ! [B_278] :
      ( k2_pre_topc('#skF_3',B_278) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_278,'#skF_3')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1499])).

tff(c_1538,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_629,c_1530])).

tff(c_1541,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1538])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_660,plain,(
    ! [C_150,A_151,B_152] :
      ( r2_hidden(C_150,A_151)
      | ~ r2_hidden(C_150,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_676,plain,(
    ! [A_156,B_157,A_158] :
      ( r2_hidden('#skF_1'(A_156,B_157),A_158)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(A_158))
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_660])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_699,plain,(
    ! [A_161,A_162] :
      ( ~ m1_subset_1(A_161,k1_zfmisc_1(A_162))
      | r1_tarski(A_161,A_162) ) ),
    inference(resolution,[status(thm)],[c_676,c_4])).

tff(c_706,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_629,c_699])).

tff(c_3479,plain,(
    ! [C_525,B_526,A_527] :
      ( C_525 = B_526
      | ~ r1_tarski(B_526,C_525)
      | ~ v2_tex_2(C_525,A_527)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ v3_tex_2(B_526,A_527)
      | ~ m1_subset_1(B_526,k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ l1_pre_topc(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3508,plain,(
    ! [A_527] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_527)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ v3_tex_2('#skF_4',A_527)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_527)))
      | ~ l1_pre_topc(A_527) ) ),
    inference(resolution,[status(thm)],[c_706,c_3479])).

tff(c_3543,plain,(
    ! [A_537] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_537)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_537)))
      | ~ v3_tex_2('#skF_4',A_537)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_537)))
      | ~ l1_pre_topc(A_537) ) ),
    inference(splitLeft,[status(thm)],[c_3508])).

tff(c_3546,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_3543])).

tff(c_3549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_629,c_627,c_614,c_70,c_1453,c_3546])).

tff(c_3550,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3508])).

tff(c_1480,plain,(
    ! [A_273] :
      ( k2_pre_topc(A_273,u1_struct_0(A_273)) = u1_struct_0(A_273)
      | ~ v4_pre_topc(u1_struct_0(A_273),A_273)
      | ~ l1_pre_topc(A_273) ) ),
    inference(resolution,[status(thm)],[c_70,c_1469])).

tff(c_1483,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1480])).

tff(c_1485,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_627,c_627,c_1483])).

tff(c_1486,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1485])).

tff(c_1489,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1486])).

tff(c_1493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1489])).

tff(c_1494,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1485])).

tff(c_1542,plain,(
    ! [B_279,A_280] :
      ( v1_tops_1(B_279,A_280)
      | k2_pre_topc(A_280,B_279) != k2_struct_0(A_280)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1553,plain,(
    ! [A_281] :
      ( v1_tops_1(u1_struct_0(A_281),A_281)
      | k2_pre_topc(A_281,u1_struct_0(A_281)) != k2_struct_0(A_281)
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_70,c_1542])).

tff(c_1559,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1553])).

tff(c_1562,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1494,c_627,c_1559])).

tff(c_3611,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3550,c_1562])).

tff(c_3624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1541,c_3611])).

tff(c_3625,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1538])).

tff(c_3725,plain,(
    ! [B_560,A_561] :
      ( v4_pre_topc(B_560,A_561)
      | k2_pre_topc(A_561,B_560) != B_560
      | ~ v2_pre_topc(A_561)
      | ~ m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0(A_561)))
      | ~ l1_pre_topc(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3728,plain,(
    ! [B_560] :
      ( v4_pre_topc(B_560,'#skF_3')
      | k2_pre_topc('#skF_3',B_560) != B_560
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_560,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_3725])).

tff(c_3736,plain,(
    ! [B_562] :
      ( v4_pre_topc(B_562,'#skF_3')
      | k2_pre_topc('#skF_3',B_562) != B_562
      | ~ m1_subset_1(B_562,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_3728])).

tff(c_3739,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_629,c_3736])).

tff(c_3745,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_3739])).

tff(c_3746,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1529,c_3745])).

tff(c_4229,plain,(
    ! [C_632,B_633,A_634] :
      ( C_632 = B_633
      | ~ r1_tarski(B_633,C_632)
      | ~ v2_tex_2(C_632,A_634)
      | ~ m1_subset_1(C_632,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ v3_tex_2(B_633,A_634)
      | ~ m1_subset_1(B_633,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4239,plain,(
    ! [A_634] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_634)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ v3_tex_2('#skF_4',A_634)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(resolution,[status(thm)],[c_706,c_4229])).

tff(c_4278,plain,(
    ! [A_637] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_637)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_637)))
      | ~ v3_tex_2('#skF_4',A_637)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_637)))
      | ~ l1_pre_topc(A_637) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3746,c_4239])).

tff(c_4281,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_4278])).

tff(c_4284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_629,c_627,c_614,c_70,c_1453,c_4281])).

tff(c_4285,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1525])).

tff(c_4291,plain,(
    ! [B_638] :
      ( k2_pre_topc('#skF_3',B_638) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_638,'#skF_3')
      | ~ m1_subset_1(B_638,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1499])).

tff(c_4294,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_629,c_4291])).

tff(c_4300,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4285,c_4294])).

tff(c_4303,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4300])).

tff(c_4323,plain,(
    ! [B_645,A_646] :
      ( v1_tops_1(B_645,A_646)
      | k2_pre_topc(A_646,B_645) != k2_struct_0(A_646)
      | ~ m1_subset_1(B_645,k1_zfmisc_1(u1_struct_0(A_646)))
      | ~ l1_pre_topc(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4326,plain,(
    ! [B_645] :
      ( v1_tops_1(B_645,'#skF_3')
      | k2_pre_topc('#skF_3',B_645) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_645,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_4323])).

tff(c_4348,plain,(
    ! [B_649] :
      ( v1_tops_1(B_649,'#skF_3')
      | k2_pre_topc('#skF_3',B_649) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_649,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4326])).

tff(c_4351,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_629,c_4348])).

tff(c_4357,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4285,c_4351])).

tff(c_4358,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4303,c_4357])).

tff(c_4926,plain,(
    ! [C_735,B_736,A_737] :
      ( C_735 = B_736
      | ~ r1_tarski(B_736,C_735)
      | ~ v2_tex_2(C_735,A_737)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(u1_struct_0(A_737)))
      | ~ v3_tex_2(B_736,A_737)
      | ~ m1_subset_1(B_736,k1_zfmisc_1(u1_struct_0(A_737)))
      | ~ l1_pre_topc(A_737) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4938,plain,(
    ! [A_737] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_737)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_737)))
      | ~ v3_tex_2('#skF_4',A_737)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_737)))
      | ~ l1_pre_topc(A_737) ) ),
    inference(resolution,[status(thm)],[c_706,c_4926])).

tff(c_4951,plain,(
    ! [A_738] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_738)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ v3_tex_2('#skF_4',A_738)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ l1_pre_topc(A_738) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4358,c_4938])).

tff(c_4954,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_4951])).

tff(c_4957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_629,c_627,c_614,c_70,c_1453,c_4954])).

tff(c_4958,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4300])).

tff(c_613,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_628,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_613])).

tff(c_4969,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4958,c_628])).

tff(c_4978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_4969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:34:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.68/3.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.60  
% 9.68/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.61  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.68/3.61  
% 9.68/3.61  %Foreground sorts:
% 9.68/3.61  
% 9.68/3.61  
% 9.68/3.61  %Background operators:
% 9.68/3.61  
% 9.68/3.61  
% 9.68/3.61  %Foreground operators:
% 9.68/3.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.68/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.68/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.68/3.61  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 9.68/3.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.68/3.61  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 9.68/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.68/3.61  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 9.68/3.61  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 9.68/3.61  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.68/3.61  tff('#skF_3', type, '#skF_3': $i).
% 9.68/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.68/3.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.68/3.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.68/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.68/3.61  tff('#skF_4', type, '#skF_4': $i).
% 9.68/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.68/3.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.68/3.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.68/3.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.68/3.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.68/3.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.68/3.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.68/3.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.68/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.68/3.61  
% 9.89/3.65  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.89/3.65  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 9.89/3.65  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 9.89/3.65  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.89/3.65  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.89/3.65  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 9.89/3.65  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 9.89/3.65  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.89/3.65  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.89/3.65  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 9.89/3.65  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 9.89/3.65  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 9.89/3.65  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 9.89/3.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.89/3.65  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.89/3.65  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.89/3.65  tff(c_14, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.89/3.65  tff(c_69, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 9.89/3.65  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.89/3.65  tff(c_617, plain, (![A_136]: (u1_struct_0(A_136)=k2_struct_0(A_136) | ~l1_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.89/3.65  tff(c_623, plain, (![A_138]: (u1_struct_0(A_138)=k2_struct_0(A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_18, c_617])).
% 9.89/3.65  tff(c_627, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_623])).
% 9.89/3.65  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_629, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_52])).
% 9.89/3.65  tff(c_62, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_83, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 9.89/3.65  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_84, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.89/3.65  tff(c_90, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_18, c_84])).
% 9.89/3.65  tff(c_94, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_90])).
% 9.89/3.65  tff(c_68, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_100, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68])).
% 9.89/3.65  tff(c_101, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_83, c_100])).
% 9.89/3.65  tff(c_95, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_52])).
% 9.89/3.65  tff(c_115, plain, (![B_58, A_59]: (v1_subset_1(B_58, A_59) | B_58=A_59 | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.89/3.65  tff(c_118, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_95, c_115])).
% 9.89/3.65  tff(c_124, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_101, c_118])).
% 9.89/3.65  tff(c_20, plain, (![A_15]: (v4_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.89/3.65  tff(c_136, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_20])).
% 9.89/3.65  tff(c_140, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_136])).
% 9.89/3.65  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.89/3.65  tff(c_70, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 9.89/3.65  tff(c_131, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_94])).
% 9.89/3.65  tff(c_203, plain, (![A_75, B_76]: (k2_pre_topc(A_75, B_76)=B_76 | ~v4_pre_topc(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.89/3.65  tff(c_206, plain, (![B_76]: (k2_pre_topc('#skF_3', B_76)=B_76 | ~v4_pre_topc(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_203])).
% 9.89/3.65  tff(c_214, plain, (![B_77]: (k2_pre_topc('#skF_3', B_77)=B_77 | ~v4_pre_topc(B_77, '#skF_3') | ~m1_subset_1(B_77, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_206])).
% 9.89/3.65  tff(c_218, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_214])).
% 9.89/3.65  tff(c_221, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_218])).
% 9.89/3.65  tff(c_250, plain, (![B_82, A_83]: (v1_tops_1(B_82, A_83) | k2_pre_topc(A_83, B_82)!=k2_struct_0(A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.89/3.65  tff(c_253, plain, (![B_82]: (v1_tops_1(B_82, '#skF_3') | k2_pre_topc('#skF_3', B_82)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_250])).
% 9.89/3.65  tff(c_261, plain, (![B_84]: (v1_tops_1(B_84, '#skF_3') | k2_pre_topc('#skF_3', B_84)!='#skF_4' | ~m1_subset_1(B_84, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_124, c_253])).
% 9.89/3.65  tff(c_265, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_70, c_261])).
% 9.89/3.65  tff(c_268, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_265])).
% 9.89/3.65  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_56, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.89/3.65  tff(c_322, plain, (![B_99, A_100]: (v2_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v1_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.89/3.65  tff(c_325, plain, (![B_99]: (v2_tex_2(B_99, '#skF_3') | ~m1_subset_1(B_99, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_322])).
% 9.89/3.65  tff(c_331, plain, (![B_99]: (v2_tex_2(B_99, '#skF_3') | ~m1_subset_1(B_99, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_325])).
% 9.89/3.65  tff(c_334, plain, (![B_101]: (v2_tex_2(B_101, '#skF_3') | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_331])).
% 9.89/3.65  tff(c_339, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_334])).
% 9.89/3.65  tff(c_583, plain, (![B_133, A_134]: (v3_tex_2(B_133, A_134) | ~v2_tex_2(B_133, A_134) | ~v1_tops_1(B_133, A_134) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.89/3.65  tff(c_589, plain, (![B_133]: (v3_tex_2(B_133, '#skF_3') | ~v2_tex_2(B_133, '#skF_3') | ~v1_tops_1(B_133, '#skF_3') | ~m1_subset_1(B_133, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_583])).
% 9.89/3.65  tff(c_596, plain, (![B_133]: (v3_tex_2(B_133, '#skF_3') | ~v2_tex_2(B_133, '#skF_3') | ~v1_tops_1(B_133, '#skF_3') | ~m1_subset_1(B_133, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_589])).
% 9.89/3.65  tff(c_599, plain, (![B_135]: (v3_tex_2(B_135, '#skF_3') | ~v2_tex_2(B_135, '#skF_3') | ~v1_tops_1(B_135, '#skF_3') | ~m1_subset_1(B_135, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_596])).
% 9.89/3.65  tff(c_606, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_599])).
% 9.89/3.65  tff(c_610, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_339, c_606])).
% 9.89/3.65  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_610])).
% 9.89/3.65  tff(c_614, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 9.89/3.65  tff(c_688, plain, (![B_159, A_160]: (v2_tex_2(B_159, A_160) | ~v3_tex_2(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.89/3.65  tff(c_709, plain, (![A_163]: (v2_tex_2(u1_struct_0(A_163), A_163) | ~v3_tex_2(u1_struct_0(A_163), A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_70, c_688])).
% 9.89/3.65  tff(c_712, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_709])).
% 9.89/3.65  tff(c_714, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_627, c_712])).
% 9.89/3.65  tff(c_715, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_714])).
% 9.89/3.65  tff(c_728, plain, (![A_165, B_166]: (k2_pre_topc(A_165, B_166)=B_166 | ~v4_pre_topc(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.89/3.65  tff(c_739, plain, (![A_167]: (k2_pre_topc(A_167, u1_struct_0(A_167))=u1_struct_0(A_167) | ~v4_pre_topc(u1_struct_0(A_167), A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_70, c_728])).
% 9.89/3.65  tff(c_742, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_739])).
% 9.89/3.65  tff(c_744, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_627, c_627, c_742])).
% 9.89/3.65  tff(c_756, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_744])).
% 9.89/3.65  tff(c_759, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_756])).
% 9.89/3.65  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_759])).
% 9.89/3.65  tff(c_764, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_744])).
% 9.89/3.65  tff(c_790, plain, (![B_172, A_173]: (v1_tops_1(B_172, A_173) | k2_pre_topc(A_173, B_172)!=k2_struct_0(A_173) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.89/3.65  tff(c_801, plain, (![A_174]: (v1_tops_1(u1_struct_0(A_174), A_174) | k2_pre_topc(A_174, u1_struct_0(A_174))!=k2_struct_0(A_174) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_70, c_790])).
% 9.89/3.65  tff(c_807, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_801])).
% 9.89/3.65  tff(c_810, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_764, c_627, c_807])).
% 9.89/3.65  tff(c_857, plain, (![B_183, A_184]: (v2_tex_2(B_183, A_184) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184) | ~v1_tdlat_3(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.89/3.65  tff(c_860, plain, (![B_183]: (v2_tex_2(B_183, '#skF_3') | ~m1_subset_1(B_183, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_857])).
% 9.89/3.65  tff(c_866, plain, (![B_183]: (v2_tex_2(B_183, '#skF_3') | ~m1_subset_1(B_183, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_860])).
% 9.89/3.65  tff(c_873, plain, (![B_186]: (v2_tex_2(B_186, '#skF_3') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_866])).
% 9.89/3.65  tff(c_883, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_70, c_873])).
% 9.89/3.65  tff(c_1425, plain, (![B_267, A_268]: (v3_tex_2(B_267, A_268) | ~v2_tex_2(B_267, A_268) | ~v1_tops_1(B_267, A_268) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.89/3.65  tff(c_1428, plain, (![B_267]: (v3_tex_2(B_267, '#skF_3') | ~v2_tex_2(B_267, '#skF_3') | ~v1_tops_1(B_267, '#skF_3') | ~m1_subset_1(B_267, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_1425])).
% 9.89/3.65  tff(c_1434, plain, (![B_267]: (v3_tex_2(B_267, '#skF_3') | ~v2_tex_2(B_267, '#skF_3') | ~v1_tops_1(B_267, '#skF_3') | ~m1_subset_1(B_267, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1428])).
% 9.89/3.65  tff(c_1437, plain, (![B_269]: (v3_tex_2(B_269, '#skF_3') | ~v2_tex_2(B_269, '#skF_3') | ~v1_tops_1(B_269, '#skF_3') | ~m1_subset_1(B_269, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1434])).
% 9.89/3.65  tff(c_1444, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_70, c_1437])).
% 9.89/3.65  tff(c_1450, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_810, c_883, c_1444])).
% 9.89/3.65  tff(c_1452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_715, c_1450])).
% 9.89/3.65  tff(c_1453, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_714])).
% 9.89/3.65  tff(c_1469, plain, (![A_271, B_272]: (k2_pre_topc(A_271, B_272)=B_272 | ~v4_pre_topc(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.89/3.65  tff(c_1472, plain, (![B_272]: (k2_pre_topc('#skF_3', B_272)=B_272 | ~v4_pre_topc(B_272, '#skF_3') | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_1469])).
% 9.89/3.65  tff(c_1517, plain, (![B_277]: (k2_pre_topc('#skF_3', B_277)=B_277 | ~v4_pre_topc(B_277, '#skF_3') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1472])).
% 9.89/3.65  tff(c_1525, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_629, c_1517])).
% 9.89/3.65  tff(c_1529, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1525])).
% 9.89/3.65  tff(c_1496, plain, (![A_274, B_275]: (k2_pre_topc(A_274, B_275)=k2_struct_0(A_274) | ~v1_tops_1(B_275, A_274) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.89/3.65  tff(c_1499, plain, (![B_275]: (k2_pre_topc('#skF_3', B_275)=k2_struct_0('#skF_3') | ~v1_tops_1(B_275, '#skF_3') | ~m1_subset_1(B_275, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_1496])).
% 9.89/3.65  tff(c_1530, plain, (![B_278]: (k2_pre_topc('#skF_3', B_278)=k2_struct_0('#skF_3') | ~v1_tops_1(B_278, '#skF_3') | ~m1_subset_1(B_278, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1499])).
% 9.89/3.65  tff(c_1538, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_629, c_1530])).
% 9.89/3.65  tff(c_1541, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1538])).
% 9.89/3.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.89/3.65  tff(c_660, plain, (![C_150, A_151, B_152]: (r2_hidden(C_150, A_151) | ~r2_hidden(C_150, B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.89/3.65  tff(c_676, plain, (![A_156, B_157, A_158]: (r2_hidden('#skF_1'(A_156, B_157), A_158) | ~m1_subset_1(A_156, k1_zfmisc_1(A_158)) | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_6, c_660])).
% 9.89/3.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.89/3.65  tff(c_699, plain, (![A_161, A_162]: (~m1_subset_1(A_161, k1_zfmisc_1(A_162)) | r1_tarski(A_161, A_162))), inference(resolution, [status(thm)], [c_676, c_4])).
% 9.89/3.65  tff(c_706, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_629, c_699])).
% 9.89/3.65  tff(c_3479, plain, (![C_525, B_526, A_527]: (C_525=B_526 | ~r1_tarski(B_526, C_525) | ~v2_tex_2(C_525, A_527) | ~m1_subset_1(C_525, k1_zfmisc_1(u1_struct_0(A_527))) | ~v3_tex_2(B_526, A_527) | ~m1_subset_1(B_526, k1_zfmisc_1(u1_struct_0(A_527))) | ~l1_pre_topc(A_527))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.89/3.65  tff(c_3508, plain, (![A_527]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_527) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_527))) | ~v3_tex_2('#skF_4', A_527) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_527))) | ~l1_pre_topc(A_527))), inference(resolution, [status(thm)], [c_706, c_3479])).
% 9.89/3.65  tff(c_3543, plain, (![A_537]: (~v2_tex_2(k2_struct_0('#skF_3'), A_537) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_537))) | ~v3_tex_2('#skF_4', A_537) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_537))) | ~l1_pre_topc(A_537))), inference(splitLeft, [status(thm)], [c_3508])).
% 9.89/3.65  tff(c_3546, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_3543])).
% 9.89/3.65  tff(c_3549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_629, c_627, c_614, c_70, c_1453, c_3546])).
% 9.89/3.65  tff(c_3550, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_3508])).
% 9.89/3.65  tff(c_1480, plain, (![A_273]: (k2_pre_topc(A_273, u1_struct_0(A_273))=u1_struct_0(A_273) | ~v4_pre_topc(u1_struct_0(A_273), A_273) | ~l1_pre_topc(A_273))), inference(resolution, [status(thm)], [c_70, c_1469])).
% 9.89/3.65  tff(c_1483, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_1480])).
% 9.89/3.65  tff(c_1485, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_627, c_627, c_1483])).
% 9.89/3.65  tff(c_1486, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1485])).
% 9.89/3.65  tff(c_1489, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1486])).
% 9.89/3.65  tff(c_1493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1489])).
% 9.89/3.65  tff(c_1494, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1485])).
% 9.89/3.65  tff(c_1542, plain, (![B_279, A_280]: (v1_tops_1(B_279, A_280) | k2_pre_topc(A_280, B_279)!=k2_struct_0(A_280) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.89/3.65  tff(c_1553, plain, (![A_281]: (v1_tops_1(u1_struct_0(A_281), A_281) | k2_pre_topc(A_281, u1_struct_0(A_281))!=k2_struct_0(A_281) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_70, c_1542])).
% 9.89/3.65  tff(c_1559, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_1553])).
% 9.89/3.65  tff(c_1562, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1494, c_627, c_1559])).
% 9.89/3.65  tff(c_3611, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3550, c_1562])).
% 9.89/3.65  tff(c_3624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1541, c_3611])).
% 9.89/3.65  tff(c_3625, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1538])).
% 9.89/3.65  tff(c_3725, plain, (![B_560, A_561]: (v4_pre_topc(B_560, A_561) | k2_pre_topc(A_561, B_560)!=B_560 | ~v2_pre_topc(A_561) | ~m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0(A_561))) | ~l1_pre_topc(A_561))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.89/3.65  tff(c_3728, plain, (![B_560]: (v4_pre_topc(B_560, '#skF_3') | k2_pre_topc('#skF_3', B_560)!=B_560 | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_560, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_3725])).
% 9.89/3.65  tff(c_3736, plain, (![B_562]: (v4_pre_topc(B_562, '#skF_3') | k2_pre_topc('#skF_3', B_562)!=B_562 | ~m1_subset_1(B_562, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_3728])).
% 9.89/3.65  tff(c_3739, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_629, c_3736])).
% 9.89/3.65  tff(c_3745, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3625, c_3739])).
% 9.89/3.65  tff(c_3746, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1529, c_3745])).
% 9.89/3.65  tff(c_4229, plain, (![C_632, B_633, A_634]: (C_632=B_633 | ~r1_tarski(B_633, C_632) | ~v2_tex_2(C_632, A_634) | ~m1_subset_1(C_632, k1_zfmisc_1(u1_struct_0(A_634))) | ~v3_tex_2(B_633, A_634) | ~m1_subset_1(B_633, k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(A_634))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.89/3.65  tff(c_4239, plain, (![A_634]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_634) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_634))) | ~v3_tex_2('#skF_4', A_634) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(A_634))), inference(resolution, [status(thm)], [c_706, c_4229])).
% 9.89/3.65  tff(c_4278, plain, (![A_637]: (~v2_tex_2(k2_struct_0('#skF_3'), A_637) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_637))) | ~v3_tex_2('#skF_4', A_637) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_637))) | ~l1_pre_topc(A_637))), inference(negUnitSimplification, [status(thm)], [c_3746, c_4239])).
% 9.89/3.65  tff(c_4281, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_4278])).
% 9.89/3.65  tff(c_4284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_629, c_627, c_614, c_70, c_1453, c_4281])).
% 9.89/3.65  tff(c_4285, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1525])).
% 9.89/3.65  tff(c_4291, plain, (![B_638]: (k2_pre_topc('#skF_3', B_638)=k2_struct_0('#skF_3') | ~v1_tops_1(B_638, '#skF_3') | ~m1_subset_1(B_638, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1499])).
% 9.89/3.65  tff(c_4294, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_629, c_4291])).
% 9.89/3.65  tff(c_4300, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4285, c_4294])).
% 9.89/3.65  tff(c_4303, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_4300])).
% 9.89/3.65  tff(c_4323, plain, (![B_645, A_646]: (v1_tops_1(B_645, A_646) | k2_pre_topc(A_646, B_645)!=k2_struct_0(A_646) | ~m1_subset_1(B_645, k1_zfmisc_1(u1_struct_0(A_646))) | ~l1_pre_topc(A_646))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.89/3.65  tff(c_4326, plain, (![B_645]: (v1_tops_1(B_645, '#skF_3') | k2_pre_topc('#skF_3', B_645)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_645, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_4323])).
% 9.89/3.65  tff(c_4348, plain, (![B_649]: (v1_tops_1(B_649, '#skF_3') | k2_pre_topc('#skF_3', B_649)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_649, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4326])).
% 9.89/3.65  tff(c_4351, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_629, c_4348])).
% 9.89/3.65  tff(c_4357, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4285, c_4351])).
% 9.89/3.65  tff(c_4358, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4303, c_4357])).
% 9.89/3.65  tff(c_4926, plain, (![C_735, B_736, A_737]: (C_735=B_736 | ~r1_tarski(B_736, C_735) | ~v2_tex_2(C_735, A_737) | ~m1_subset_1(C_735, k1_zfmisc_1(u1_struct_0(A_737))) | ~v3_tex_2(B_736, A_737) | ~m1_subset_1(B_736, k1_zfmisc_1(u1_struct_0(A_737))) | ~l1_pre_topc(A_737))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.89/3.65  tff(c_4938, plain, (![A_737]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_737) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_737))) | ~v3_tex_2('#skF_4', A_737) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_737))) | ~l1_pre_topc(A_737))), inference(resolution, [status(thm)], [c_706, c_4926])).
% 9.89/3.65  tff(c_4951, plain, (![A_738]: (~v2_tex_2(k2_struct_0('#skF_3'), A_738) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_738))) | ~v3_tex_2('#skF_4', A_738) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_738))) | ~l1_pre_topc(A_738))), inference(negUnitSimplification, [status(thm)], [c_4358, c_4938])).
% 9.89/3.65  tff(c_4954, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_4951])).
% 9.89/3.65  tff(c_4957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_629, c_627, c_614, c_70, c_1453, c_4954])).
% 9.89/3.65  tff(c_4958, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4300])).
% 9.89/3.65  tff(c_613, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 9.89/3.65  tff(c_628, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_613])).
% 9.89/3.65  tff(c_4969, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4958, c_628])).
% 9.89/3.65  tff(c_4978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_4969])).
% 9.89/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.89/3.65  
% 9.89/3.65  Inference rules
% 9.89/3.65  ----------------------
% 9.89/3.65  #Ref     : 0
% 9.89/3.65  #Sup     : 1094
% 9.89/3.65  #Fact    : 0
% 9.89/3.65  #Define  : 0
% 9.89/3.65  #Split   : 19
% 9.89/3.65  #Chain   : 0
% 9.89/3.65  #Close   : 0
% 9.89/3.65  
% 9.89/3.65  Ordering : KBO
% 9.89/3.65  
% 9.89/3.65  Simplification rules
% 9.89/3.65  ----------------------
% 9.89/3.65  #Subsume      : 389
% 9.89/3.65  #Demod        : 777
% 9.89/3.65  #Tautology    : 195
% 9.89/3.65  #SimpNegUnit  : 51
% 9.89/3.65  #BackRed      : 128
% 9.89/3.65  
% 9.89/3.65  #Partial instantiations: 0
% 9.89/3.65  #Strategies tried      : 1
% 9.89/3.65  
% 9.89/3.65  Timing (in seconds)
% 9.89/3.65  ----------------------
% 9.89/3.66  Preprocessing        : 0.54
% 9.89/3.66  Parsing              : 0.27
% 9.89/3.66  CNF conversion       : 0.04
% 9.89/3.66  Main loop            : 2.19
% 9.89/3.66  Inferencing          : 0.72
% 9.89/3.66  Reduction            : 0.60
% 9.89/3.66  Demodulation         : 0.39
% 9.89/3.66  BG Simplification    : 0.07
% 9.89/3.66  Subsumption          : 0.64
% 9.89/3.66  Abstraction          : 0.09
% 9.89/3.66  MUC search           : 0.00
% 9.89/3.66  Cooper               : 0.00
% 9.89/3.66  Total                : 2.82
% 9.89/3.66  Index Insertion      : 0.00
% 9.89/3.66  Index Deletion       : 0.00
% 9.89/3.66  Index Matching       : 0.00
% 9.89/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
