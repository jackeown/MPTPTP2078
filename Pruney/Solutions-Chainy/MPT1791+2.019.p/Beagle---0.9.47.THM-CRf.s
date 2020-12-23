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
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 448 expanded)
%              Number of leaves         :   40 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  294 (1395 expanded)
%              Number of equality atoms :   29 ( 194 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_187,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_172,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v1_xboole_0(u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_pre_topc)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_102,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_215,plain,(
    ! [B_65,A_66] :
      ( v3_pre_topc(B_65,A_66)
      | ~ r2_hidden(B_65,u1_pre_topc(A_66))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_229,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_215])).

tff(c_238,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_229])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_238])).

tff(c_243,plain,
    ( ~ m1_subset_1('#skF_3',u1_pre_topc('#skF_2'))
    | v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_239])).

tff(c_244,plain,(
    ~ m1_subset_1('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_368,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,k5_tmap_1(A_85,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_378,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_368])).

tff(c_386,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_378])).

tff(c_387,plain,(
    r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_386])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_395,plain,(
    ~ v1_xboole_0(k5_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_387,c_2])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_394,plain,
    ( m1_subset_1('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | v1_xboole_0(k5_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_387,c_6])).

tff(c_396,plain,(
    m1_subset_1('#skF_3',k5_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_394])).

tff(c_524,plain,(
    ! [A_95,B_96] :
      ( u1_pre_topc(k6_tmap_1(A_95,B_96)) = k5_tmap_1(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_541,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_524])).

tff(c_552,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_541])).

tff(c_553,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_552])).

tff(c_287,plain,(
    ! [A_72,B_73] :
      ( l1_pre_topc(k6_tmap_1(A_72,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_301,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_287])).

tff(c_310,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_301])).

tff(c_311,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_310])).

tff(c_412,plain,(
    ! [A_88,B_89] :
      ( u1_struct_0(k6_tmap_1(A_88,B_89)) = u1_struct_0(A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_426,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_412])).

tff(c_435,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_426])).

tff(c_436,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_435])).

tff(c_20,plain,(
    ! [A_13] :
      ( m1_subset_1(u1_pre_topc(A_13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    ! [A_55,C_56,B_57] :
      ( m1_subset_1(A_55,C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_158,plain,(
    ! [A_55,A_13] :
      ( m1_subset_1(A_55,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ r2_hidden(A_55,u1_pre_topc(A_13))
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_147])).

tff(c_457,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_55,u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_158])).

tff(c_482,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_55,u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_457])).

tff(c_606,plain,(
    ! [A_97] :
      ( m1_subset_1(A_97,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_97,k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_482])).

tff(c_50,plain,(
    ! [B_30,A_28] :
      ( r2_hidden(B_30,k5_tmap_1(A_28,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_614,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,k5_tmap_1('#skF_2',A_97))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_97,k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_606,c_50])).

tff(c_642,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,k5_tmap_1('#skF_2',A_97))
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_97,k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_614])).

tff(c_755,plain,(
    ! [A_103] :
      ( r2_hidden(A_103,k5_tmap_1('#skF_2',A_103))
      | ~ r2_hidden(A_103,k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_642])).

tff(c_760,plain,(
    ! [B_6] :
      ( r2_hidden(B_6,k5_tmap_1('#skF_2',B_6))
      | ~ m1_subset_1(B_6,k5_tmap_1('#skF_2','#skF_3'))
      | v1_xboole_0(k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_755])).

tff(c_768,plain,(
    ! [B_6] :
      ( r2_hidden(B_6,k5_tmap_1('#skF_2',B_6))
      | ~ m1_subset_1(B_6,k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_760])).

tff(c_466,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_20])).

tff(c_488,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_466])).

tff(c_555,plain,(
    m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_488])).

tff(c_34,plain,(
    ! [A_19] : u1_struct_0(k2_yellow_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    ! [B_22,A_20] :
      ( m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_20)))))
      | ~ v1_tops_2(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20))))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_827,plain,(
    ! [B_108,A_109] :
      ( m1_subset_1(B_108,k1_zfmisc_1(u1_pre_topc(A_109)))
      | ~ v1_tops_2(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109))))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_830,plain,
    ( m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_pre_topc('#skF_2')))
    | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_555,c_827])).

tff(c_854,plain,
    ( m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_pre_topc('#skF_2')))
    | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_830])).

tff(c_1124,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_854])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_tops_2(u1_pre_topc(A_15),A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_577,plain,
    ( v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_24])).

tff(c_595,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_577])).

tff(c_74,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_134,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_74])).

tff(c_2044,plain,(
    ! [B_145,A_146] :
      ( v1_tops_2(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_146),u1_pre_topc(A_146))))))
      | ~ v1_tops_2(B_145,g1_pre_topc(u1_struct_0(A_146),u1_pre_topc(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2077,plain,(
    ! [B_145] :
      ( v1_tops_2(B_145,'#skF_2')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_tops_2(B_145,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2044])).

tff(c_2104,plain,(
    ! [B_145] :
      ( v1_tops_2(B_145,'#skF_2')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_145,k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_134,c_436,c_2077])).

tff(c_2146,plain,(
    ! [B_148] :
      ( v1_tops_2(B_148,'#skF_2')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_148,k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2104])).

tff(c_2156,plain,
    ( v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_555,c_2146])).

tff(c_2177,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_2156])).

tff(c_2179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1124,c_2177])).

tff(c_2180,plain,(
    m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_854])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2191,plain,(
    ! [A_149] :
      ( m1_subset_1(A_149,u1_pre_topc('#skF_2'))
      | ~ r2_hidden(A_149,k5_tmap_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2180,c_14])).

tff(c_2195,plain,
    ( m1_subset_1('#skF_3',u1_pre_topc('#skF_2'))
    | ~ m1_subset_1('#skF_3',k5_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_768,c_2191])).

tff(c_2209,plain,(
    m1_subset_1('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_2195])).

tff(c_2211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_2209])).

tff(c_2212,plain,(
    v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_22,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_pre_topc(A_14))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2216,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2212,c_22])).

tff(c_2220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2216])).

tff(c_2221,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2222,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2318,plain,(
    ! [B_171,A_172] :
      ( r2_hidden(B_171,u1_pre_topc(A_172))
      | ~ v3_pre_topc(B_171,A_172)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2332,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2318])).

tff(c_2341,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2222,c_2332])).

tff(c_3848,plain,(
    ! [A_248,B_249] :
      ( k5_tmap_1(A_248,B_249) = u1_pre_topc(A_248)
      | ~ r2_hidden(B_249,u1_pre_topc(A_248))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3882,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_3848])).

tff(c_3905,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2341,c_3882])).

tff(c_3906,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3905])).

tff(c_3695,plain,(
    ! [A_241,B_242] :
      ( g1_pre_topc(u1_struct_0(A_241),k5_tmap_1(A_241,B_242)) = k6_tmap_1(A_241,B_242)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3719,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_3695])).

tff(c_3741,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_3719])).

tff(c_3742,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3741])).

tff(c_3912,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_3742])).

tff(c_3941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2221,c_3912])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.09  
% 5.35/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.09  %$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_2 > #skF_3
% 5.35/2.09  
% 5.35/2.09  %Foreground sorts:
% 5.35/2.09  
% 5.35/2.09  
% 5.35/2.09  %Background operators:
% 5.35/2.09  
% 5.35/2.09  
% 5.35/2.09  %Foreground operators:
% 5.35/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.35/2.09  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.35/2.09  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.35/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.09  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.35/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.35/2.09  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 5.35/2.09  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.35/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.35/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.35/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.09  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.35/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.09  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 5.35/2.09  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 5.35/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.35/2.09  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 5.35/2.09  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 5.35/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.35/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.09  
% 5.35/2.11  tff(f_187, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 5.35/2.11  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.35/2.11  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.35/2.11  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tmap_1)).
% 5.35/2.11  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.35/2.11  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 5.35/2.11  tff(f_132, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 5.35/2.11  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.35/2.11  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.35/2.11  tff(f_94, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 5.35/2.11  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_1)).
% 5.35/2.11  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => v1_tops_2(u1_pre_topc(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_compts_1)).
% 5.35/2.11  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_compts_1)).
% 5.35/2.11  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => ~v1_xboole_0(u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_pre_topc)).
% 5.35/2.11  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 5.35/2.11  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 5.35/2.11  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.35/2.11  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.35/2.11  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.11  tff(c_68, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.35/2.11  tff(c_102, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_68])).
% 5.35/2.11  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.35/2.11  tff(c_215, plain, (![B_65, A_66]: (v3_pre_topc(B_65, A_66) | ~r2_hidden(B_65, u1_pre_topc(A_66)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.35/2.11  tff(c_229, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_215])).
% 5.35/2.11  tff(c_238, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_229])).
% 5.35/2.11  tff(c_239, plain, (~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_102, c_238])).
% 5.35/2.11  tff(c_243, plain, (~m1_subset_1('#skF_3', u1_pre_topc('#skF_2')) | v1_xboole_0(u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_239])).
% 5.35/2.11  tff(c_244, plain, (~m1_subset_1('#skF_3', u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_243])).
% 5.35/2.11  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.35/2.11  tff(c_368, plain, (![B_84, A_85]: (r2_hidden(B_84, k5_tmap_1(A_85, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.35/2.11  tff(c_378, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_368])).
% 5.35/2.11  tff(c_386, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_378])).
% 5.35/2.11  tff(c_387, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_386])).
% 5.35/2.11  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.35/2.11  tff(c_395, plain, (~v1_xboole_0(k5_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_387, c_2])).
% 5.35/2.11  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.11  tff(c_394, plain, (m1_subset_1('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | v1_xboole_0(k5_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_387, c_6])).
% 5.35/2.11  tff(c_396, plain, (m1_subset_1('#skF_3', k5_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_395, c_394])).
% 5.35/2.11  tff(c_524, plain, (![A_95, B_96]: (u1_pre_topc(k6_tmap_1(A_95, B_96))=k5_tmap_1(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.35/2.11  tff(c_541, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_524])).
% 5.35/2.11  tff(c_552, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_541])).
% 5.35/2.11  tff(c_553, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_552])).
% 5.35/2.11  tff(c_287, plain, (![A_72, B_73]: (l1_pre_topc(k6_tmap_1(A_72, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.35/2.11  tff(c_301, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_287])).
% 5.35/2.11  tff(c_310, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_301])).
% 5.35/2.11  tff(c_311, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_310])).
% 5.35/2.11  tff(c_412, plain, (![A_88, B_89]: (u1_struct_0(k6_tmap_1(A_88, B_89))=u1_struct_0(A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.35/2.11  tff(c_426, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_412])).
% 5.35/2.11  tff(c_435, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_426])).
% 5.35/2.11  tff(c_436, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_435])).
% 5.35/2.11  tff(c_20, plain, (![A_13]: (m1_subset_1(u1_pre_topc(A_13), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.35/2.11  tff(c_147, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.35/2.11  tff(c_158, plain, (![A_55, A_13]: (m1_subset_1(A_55, k1_zfmisc_1(u1_struct_0(A_13))) | ~r2_hidden(A_55, u1_pre_topc(A_13)) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_20, c_147])).
% 5.35/2.11  tff(c_457, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_55, u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_436, c_158])).
% 5.35/2.11  tff(c_482, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_55, u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_457])).
% 5.35/2.11  tff(c_606, plain, (![A_97]: (m1_subset_1(A_97, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_97, k5_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_553, c_482])).
% 5.35/2.11  tff(c_50, plain, (![B_30, A_28]: (r2_hidden(B_30, k5_tmap_1(A_28, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.35/2.11  tff(c_614, plain, (![A_97]: (r2_hidden(A_97, k5_tmap_1('#skF_2', A_97)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(A_97, k5_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_606, c_50])).
% 5.35/2.11  tff(c_642, plain, (![A_97]: (r2_hidden(A_97, k5_tmap_1('#skF_2', A_97)) | v2_struct_0('#skF_2') | ~r2_hidden(A_97, k5_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_614])).
% 5.35/2.11  tff(c_755, plain, (![A_103]: (r2_hidden(A_103, k5_tmap_1('#skF_2', A_103)) | ~r2_hidden(A_103, k5_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_642])).
% 5.35/2.11  tff(c_760, plain, (![B_6]: (r2_hidden(B_6, k5_tmap_1('#skF_2', B_6)) | ~m1_subset_1(B_6, k5_tmap_1('#skF_2', '#skF_3')) | v1_xboole_0(k5_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_8, c_755])).
% 5.35/2.11  tff(c_768, plain, (![B_6]: (r2_hidden(B_6, k5_tmap_1('#skF_2', B_6)) | ~m1_subset_1(B_6, k5_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_395, c_760])).
% 5.35/2.11  tff(c_466, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_436, c_20])).
% 5.35/2.11  tff(c_488, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_466])).
% 5.35/2.11  tff(c_555, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_553, c_488])).
% 5.35/2.11  tff(c_34, plain, (![A_19]: (u1_struct_0(k2_yellow_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.35/2.11  tff(c_40, plain, (![B_22, A_20]: (m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_20))))) | ~v1_tops_2(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20)))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.35/2.11  tff(c_827, plain, (![B_108, A_109]: (m1_subset_1(B_108, k1_zfmisc_1(u1_pre_topc(A_109))) | ~v1_tops_2(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109)))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 5.35/2.11  tff(c_830, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_pre_topc('#skF_2'))) | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_555, c_827])).
% 5.35/2.11  tff(c_854, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_pre_topc('#skF_2'))) | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_830])).
% 5.35/2.11  tff(c_1124, plain, (~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_854])).
% 5.35/2.11  tff(c_24, plain, (![A_15]: (v1_tops_2(u1_pre_topc(A_15), A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.35/2.11  tff(c_577, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_24])).
% 5.35/2.11  tff(c_595, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_577])).
% 5.35/2.11  tff(c_74, plain, (v3_pre_topc('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.35/2.11  tff(c_134, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_102, c_74])).
% 5.35/2.11  tff(c_2044, plain, (![B_145, A_146]: (v1_tops_2(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_146), u1_pre_topc(A_146)))))) | ~v1_tops_2(B_145, g1_pre_topc(u1_struct_0(A_146), u1_pre_topc(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.35/2.11  tff(c_2077, plain, (![B_145]: (v1_tops_2(B_145, '#skF_2') | ~m1_subset_1(B_145, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_tops_2(B_145, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_2044])).
% 5.35/2.11  tff(c_2104, plain, (![B_145]: (v1_tops_2(B_145, '#skF_2') | ~m1_subset_1(B_145, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_145, k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_134, c_436, c_2077])).
% 5.35/2.11  tff(c_2146, plain, (![B_148]: (v1_tops_2(B_148, '#skF_2') | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_148, k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_2104])).
% 5.35/2.11  tff(c_2156, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_555, c_2146])).
% 5.35/2.11  tff(c_2177, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_595, c_2156])).
% 5.35/2.11  tff(c_2179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1124, c_2177])).
% 5.35/2.11  tff(c_2180, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_854])).
% 5.35/2.11  tff(c_14, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.35/2.11  tff(c_2191, plain, (![A_149]: (m1_subset_1(A_149, u1_pre_topc('#skF_2')) | ~r2_hidden(A_149, k5_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_2180, c_14])).
% 5.35/2.11  tff(c_2195, plain, (m1_subset_1('#skF_3', u1_pre_topc('#skF_2')) | ~m1_subset_1('#skF_3', k5_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_768, c_2191])).
% 5.35/2.11  tff(c_2209, plain, (m1_subset_1('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_2195])).
% 5.35/2.11  tff(c_2211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_2209])).
% 5.35/2.11  tff(c_2212, plain, (v1_xboole_0(u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_243])).
% 5.35/2.11  tff(c_22, plain, (![A_14]: (~v1_xboole_0(u1_pre_topc(A_14)) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.35/2.11  tff(c_2216, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2212, c_22])).
% 5.35/2.11  tff(c_2220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2216])).
% 5.35/2.11  tff(c_2221, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 5.35/2.11  tff(c_2222, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 5.35/2.11  tff(c_2318, plain, (![B_171, A_172]: (r2_hidden(B_171, u1_pre_topc(A_172)) | ~v3_pre_topc(B_171, A_172) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.35/2.11  tff(c_2332, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_2318])).
% 5.35/2.11  tff(c_2341, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2222, c_2332])).
% 5.35/2.11  tff(c_3848, plain, (![A_248, B_249]: (k5_tmap_1(A_248, B_249)=u1_pre_topc(A_248) | ~r2_hidden(B_249, u1_pre_topc(A_248)) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/2.11  tff(c_3882, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_3848])).
% 5.35/2.11  tff(c_3905, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2341, c_3882])).
% 5.35/2.11  tff(c_3906, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_3905])).
% 5.35/2.11  tff(c_3695, plain, (![A_241, B_242]: (g1_pre_topc(u1_struct_0(A_241), k5_tmap_1(A_241, B_242))=k6_tmap_1(A_241, B_242) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.35/2.11  tff(c_3719, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_3695])).
% 5.35/2.11  tff(c_3741, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_3719])).
% 5.35/2.11  tff(c_3742, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_3741])).
% 5.35/2.11  tff(c_3912, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_3742])).
% 5.35/2.11  tff(c_3941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2221, c_3912])).
% 5.35/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.11  
% 5.35/2.11  Inference rules
% 5.35/2.11  ----------------------
% 5.35/2.11  #Ref     : 0
% 5.35/2.11  #Sup     : 755
% 5.35/2.11  #Fact    : 0
% 5.35/2.11  #Define  : 0
% 5.35/2.11  #Split   : 16
% 5.35/2.11  #Chain   : 0
% 5.35/2.11  #Close   : 0
% 5.35/2.11  
% 5.35/2.11  Ordering : KBO
% 5.35/2.11  
% 5.35/2.11  Simplification rules
% 5.35/2.11  ----------------------
% 5.35/2.11  #Subsume      : 93
% 5.35/2.11  #Demod        : 674
% 5.35/2.11  #Tautology    : 126
% 5.35/2.11  #SimpNegUnit  : 146
% 5.35/2.11  #BackRed      : 47
% 5.35/2.11  
% 5.35/2.11  #Partial instantiations: 0
% 5.35/2.11  #Strategies tried      : 1
% 5.35/2.11  
% 5.35/2.11  Timing (in seconds)
% 5.35/2.11  ----------------------
% 5.35/2.11  Preprocessing        : 0.43
% 5.35/2.11  Parsing              : 0.26
% 5.35/2.11  CNF conversion       : 0.03
% 5.35/2.11  Main loop            : 0.87
% 5.66/2.11  Inferencing          : 0.28
% 5.66/2.11  Reduction            : 0.32
% 5.66/2.11  Demodulation         : 0.22
% 5.66/2.11  BG Simplification    : 0.04
% 5.66/2.12  Subsumption          : 0.15
% 5.66/2.12  Abstraction          : 0.04
% 5.66/2.12  MUC search           : 0.00
% 5.66/2.12  Cooper               : 0.00
% 5.66/2.12  Total                : 1.34
% 5.66/2.12  Index Insertion      : 0.00
% 5.66/2.12  Index Deletion       : 0.00
% 5.66/2.12  Index Matching       : 0.00
% 5.66/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
