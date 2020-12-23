%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:02 EST 2020

% Result     : Theorem 11.77s
% Output     : CNFRefutation 12.35s
% Verified   : 
% Statistics : Number of formulae       :  458 (5948 expanded)
%              Number of leaves         :   32 (1754 expanded)
%              Depth                    :   21
%              Number of atoms          : 1126 (19004 expanded)
%              Number of equality atoms :  207 (1383 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_compts_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v2_compts_1(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( B = k1_xboole_0
             => ( v2_compts_1(B,A)
              <=> v1_compts_1(k1_pre_topc(A,B)) ) )
            & ( v2_pre_topc(A)
             => ( B = k1_xboole_0
                | ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_101,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [A_37,B_38] :
      ( l1_pre_topc(g1_pre_topc(A_37,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_16] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_65,plain,(
    ! [A_34,B_35] :
      ( v1_pre_topc(g1_pre_topc(A_34,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [A_16] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8335,plain,(
    ! [C_392,A_393,D_394,B_395] :
      ( C_392 = A_393
      | g1_pre_topc(C_392,D_394) != g1_pre_topc(A_393,B_395)
      | ~ m1_subset_1(B_395,k1_zfmisc_1(k1_zfmisc_1(A_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8337,plain,(
    ! [A_1,A_393,B_395] :
      ( u1_struct_0(A_1) = A_393
      | g1_pre_topc(A_393,B_395) != A_1
      | ~ m1_subset_1(B_395,k1_zfmisc_1(k1_zfmisc_1(A_393)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8335])).

tff(c_14505,plain,(
    ! [A_646,B_647] :
      ( u1_struct_0(g1_pre_topc(A_646,B_647)) = A_646
      | ~ m1_subset_1(B_647,k1_zfmisc_1(k1_zfmisc_1(A_646)))
      | ~ v1_pre_topc(g1_pre_topc(A_646,B_647))
      | ~ l1_pre_topc(g1_pre_topc(A_646,B_647)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8337])).

tff(c_14515,plain,(
    ! [A_650] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_650),u1_pre_topc(A_650))) = u1_struct_0(A_650)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_650),u1_pre_topc(A_650)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_650),u1_pre_topc(A_650)))
      | ~ l1_pre_topc(A_650) ) ),
    inference(resolution,[status(thm)],[c_18,c_14505])).

tff(c_14523,plain,(
    ! [A_651] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_651),u1_pre_topc(A_651))) = u1_struct_0(A_651)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_651),u1_pre_topc(A_651)))
      | ~ l1_pre_topc(A_651) ) ),
    inference(resolution,[status(thm)],[c_69,c_14515])).

tff(c_14531,plain,(
    ! [A_652] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_652),u1_pre_topc(A_652))) = u1_struct_0(A_652)
      | ~ l1_pre_topc(A_652) ) ),
    inference(resolution,[status(thm)],[c_75,c_14523])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_20,plain,(
    ! [A_17] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_pre_topc(k1_pre_topc(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8304,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_12])).

tff(c_8310,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8304])).

tff(c_62,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_77,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8382,plain,(
    ! [A_408,B_409] :
      ( v1_compts_1(k1_pre_topc(A_408,B_409))
      | ~ v2_compts_1(B_409,A_408)
      | k1_xboole_0 = B_409
      | ~ v2_pre_topc(A_408)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8385,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_8382])).

tff(c_8388,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_77,c_8385])).

tff(c_8396,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8388])).

tff(c_38,plain,(
    ! [A_27] :
      ( v1_compts_1(k1_pre_topc(A_27,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_27)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8405,plain,(
    ! [A_412] :
      ( v1_compts_1(k1_pre_topc(A_412,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_412)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_412)))
      | ~ l1_pre_topc(A_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8396,c_8396,c_8396,c_38])).

tff(c_8408,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_8405])).

tff(c_8411,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_77,c_8408])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8317,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8310,c_16])).

tff(c_8320,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8317])).

tff(c_30,plain,(
    ! [A_24,B_26] :
      ( m1_pre_topc(A_24,g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(A_24,B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8480,plain,(
    ! [A_430,B_431] :
      ( u1_struct_0(g1_pre_topc(A_430,B_431)) = A_430
      | ~ m1_subset_1(B_431,k1_zfmisc_1(k1_zfmisc_1(A_430)))
      | ~ v1_pre_topc(g1_pre_topc(A_430,B_431))
      | ~ l1_pre_topc(g1_pre_topc(A_430,B_431)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8337])).

tff(c_8493,plain,(
    ! [A_433] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_433),u1_pre_topc(A_433))) = u1_struct_0(A_433)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_433),u1_pre_topc(A_433)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_433),u1_pre_topc(A_433)))
      | ~ l1_pre_topc(A_433) ) ),
    inference(resolution,[status(thm)],[c_18,c_8480])).

tff(c_8501,plain,(
    ! [A_434] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_434),u1_pre_topc(A_434))) = u1_struct_0(A_434)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_434),u1_pre_topc(A_434)))
      | ~ l1_pre_topc(A_434) ) ),
    inference(resolution,[status(thm)],[c_69,c_8493])).

tff(c_8512,plain,(
    ! [A_437] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_437),u1_pre_topc(A_437))) = u1_struct_0(A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(resolution,[status(thm)],[c_75,c_8501])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_pre_topc(k1_pre_topc(A_11,B_12))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8307,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_14])).

tff(c_8313,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8307])).

tff(c_8440,plain,(
    ! [A_422,B_423] :
      ( k2_struct_0(k1_pre_topc(A_422,B_423)) = B_423
      | ~ m1_pre_topc(k1_pre_topc(A_422,B_423),A_422)
      | ~ v1_pre_topc(k1_pre_topc(A_422,B_423))
      | ~ m1_subset_1(B_423,k1_zfmisc_1(u1_struct_0(A_422)))
      | ~ l1_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8445,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8310,c_8440])).

tff(c_8449,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101,c_8313,c_8445])).

tff(c_4,plain,(
    ! [A_2,C_8] :
      ( k1_pre_topc(A_2,k2_struct_0(C_8)) = C_8
      | ~ m1_pre_topc(C_8,A_2)
      | ~ v1_pre_topc(C_8)
      | ~ m1_subset_1(k2_struct_0(C_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8453,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8449,c_4])).

tff(c_8457,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8313,c_8449,c_8453])).

tff(c_8589,plain,(
    ! [A_439] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_439),u1_pre_topc(A_439)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0(A_439),u1_pre_topc(A_439)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_439),u1_pre_topc(A_439)))
      | ~ l1_pre_topc(A_439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8512,c_8457])).

tff(c_8596,plain,(
    ! [B_26] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_8589])).

tff(c_10444,plain,(
    ! [B_501] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_501),u1_pre_topc(B_501)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_501)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_501),u1_pre_topc(B_501)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_501)
      | ~ l1_pre_topc(B_501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8320,c_8596])).

tff(c_10470,plain,(
    ! [A_502] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_502),u1_pre_topc(A_502)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_502)
      | ~ l1_pre_topc(A_502) ) ),
    inference(resolution,[status(thm)],[c_75,c_10444])).

tff(c_36,plain,(
    ! [A_27] :
      ( v2_compts_1(k1_xboole_0,A_27)
      | ~ v1_compts_1(k1_pre_topc(A_27,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8400,plain,(
    ! [A_27] :
      ( v2_compts_1('#skF_3',A_27)
      | ~ v1_compts_1(k1_pre_topc(A_27,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8396,c_8396,c_8396,c_36])).

tff(c_8537,plain,(
    ! [A_437] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_437),u1_pre_topc(A_437)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_437),u1_pre_topc(A_437)),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_437),u1_pre_topc(A_437)))
      | ~ l1_pre_topc(A_437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8512,c_8400])).

tff(c_10483,plain,(
    ! [A_502] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_502),u1_pre_topc(A_502)))
      | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_502),u1_pre_topc(A_502)))
      | ~ l1_pre_topc(A_502)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_502)
      | ~ l1_pre_topc(A_502) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10470,c_8537])).

tff(c_10540,plain,(
    ! [A_503] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_503),u1_pre_topc(A_503)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_503),u1_pre_topc(A_503)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_503)
      | ~ l1_pre_topc(A_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8411,c_10483])).

tff(c_50,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8358,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_10543,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10540,c_8358])).

tff(c_10567,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8310,c_101,c_10543])).

tff(c_10573,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_10567])).

tff(c_10579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10573])).

tff(c_10581,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8388])).

tff(c_10580,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8388])).

tff(c_10601,plain,(
    ! [A_512,B_513] :
      ( u1_struct_0(g1_pre_topc(A_512,B_513)) = A_512
      | ~ m1_subset_1(B_513,k1_zfmisc_1(k1_zfmisc_1(A_512)))
      | ~ v1_pre_topc(g1_pre_topc(A_512,B_513))
      | ~ l1_pre_topc(g1_pre_topc(A_512,B_513)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8337])).

tff(c_10740,plain,(
    ! [A_525] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_525),u1_pre_topc(A_525))) = u1_struct_0(A_525)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_525),u1_pre_topc(A_525)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_525),u1_pre_topc(A_525)))
      | ~ l1_pre_topc(A_525) ) ),
    inference(resolution,[status(thm)],[c_18,c_10601])).

tff(c_10751,plain,(
    ! [A_526] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_526),u1_pre_topc(A_526))) = u1_struct_0(A_526)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_526),u1_pre_topc(A_526)))
      | ~ l1_pre_topc(A_526) ) ),
    inference(resolution,[status(thm)],[c_69,c_10740])).

tff(c_10767,plain,(
    ! [A_529] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_529),u1_pre_topc(A_529))) = u1_struct_0(A_529)
      | ~ l1_pre_topc(A_529) ) ),
    inference(resolution,[status(thm)],[c_75,c_10751])).

tff(c_10611,plain,(
    ! [A_516,B_517] :
      ( k2_struct_0(k1_pre_topc(A_516,B_517)) = B_517
      | ~ m1_pre_topc(k1_pre_topc(A_516,B_517),A_516)
      | ~ v1_pre_topc(k1_pre_topc(A_516,B_517))
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ l1_pre_topc(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10616,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8310,c_10611])).

tff(c_10620,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101,c_8313,c_10616])).

tff(c_10624,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10620,c_4])).

tff(c_10628,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8313,c_10620,c_10624])).

tff(c_10874,plain,(
    ! [A_531] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_531),u1_pre_topc(A_531)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0(A_531),u1_pre_topc(A_531)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_531)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_531),u1_pre_topc(A_531)))
      | ~ l1_pre_topc(A_531) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10767,c_10628])).

tff(c_10884,plain,(
    ! [B_26] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_10874])).

tff(c_12521,plain,(
    ! [B_585] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_585),u1_pre_topc(B_585)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_585)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_585),u1_pre_topc(B_585)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_585)
      | ~ l1_pre_topc(B_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8320,c_10884])).

tff(c_12546,plain,(
    ! [A_16] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_75,c_12521])).

tff(c_32,plain,(
    ! [B_29,A_27] :
      ( v2_compts_1(B_29,A_27)
      | ~ v1_compts_1(k1_pre_topc(A_27,B_29))
      | k1_xboole_0 = B_29
      | ~ v2_pre_topc(A_27)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_14197,plain,(
    ! [B_616,A_617] :
      ( v2_compts_1(B_616,g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617)),B_616))
      | k1_xboole_0 = B_616
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617)))
      | ~ m1_subset_1(B_616,k1_zfmisc_1(u1_struct_0(A_617)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_617),u1_pre_topc(A_617)))
      | ~ l1_pre_topc(A_617) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10767,c_32])).

tff(c_14209,plain,(
    ! [A_16] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
      | k1_xboole_0 = '#skF_3'
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12546,c_14197])).

tff(c_14235,plain,(
    ! [A_16] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | k1_xboole_0 = '#skF_3'
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10580,c_14209])).

tff(c_14239,plain,(
    ! [A_618] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_618),u1_pre_topc(A_618)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_618),u1_pre_topc(A_618)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_618),u1_pre_topc(A_618)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_618)
      | ~ l1_pre_topc(A_618) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10581,c_14235])).

tff(c_14242,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14239,c_8358])).

tff(c_14272,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8310,c_101,c_14242])).

tff(c_14273,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14272])).

tff(c_14279,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_14273])).

tff(c_14285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14279])).

tff(c_14286,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14272])).

tff(c_14374,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_14286])).

tff(c_14381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_14374])).

tff(c_14383,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_102,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_124,plain,(
    ! [C_46,A_47,D_48,B_49] :
      ( C_46 = A_47
      | g1_pre_topc(C_46,D_48) != g1_pre_topc(A_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_126,plain,(
    ! [A_1,A_47,B_49] :
      ( u1_struct_0(A_1) = A_47
      | g1_pre_topc(A_47,B_49) != A_1
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_47)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_6295,plain,(
    ! [A_310,B_311] :
      ( u1_struct_0(g1_pre_topc(A_310,B_311)) = A_310
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k1_zfmisc_1(A_310)))
      | ~ v1_pre_topc(g1_pre_topc(A_310,B_311))
      | ~ l1_pre_topc(g1_pre_topc(A_310,B_311)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_126])).

tff(c_6308,plain,(
    ! [A_313] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_313),u1_pre_topc(A_313))) = u1_struct_0(A_313)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_313),u1_pre_topc(A_313)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_313),u1_pre_topc(A_313)))
      | ~ l1_pre_topc(A_313) ) ),
    inference(resolution,[status(thm)],[c_18,c_6295])).

tff(c_6316,plain,(
    ! [A_314] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_314),u1_pre_topc(A_314))) = u1_struct_0(A_314)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_314),u1_pre_topc(A_314)))
      | ~ l1_pre_topc(A_314) ) ),
    inference(resolution,[status(thm)],[c_69,c_6308])).

tff(c_6324,plain,(
    ! [A_315] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_315),u1_pre_topc(A_315))) = u1_struct_0(A_315)
      | ~ l1_pre_topc(A_315) ) ),
    inference(resolution,[status(thm)],[c_75,c_6316])).

tff(c_104,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_12])).

tff(c_110,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_104])).

tff(c_182,plain,(
    ! [A_68,B_69] :
      ( v1_compts_1(k1_pre_topc(A_68,B_69))
      | ~ v2_compts_1(B_69,A_68)
      | k1_xboole_0 = B_69
      | ~ v2_pre_topc(A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_185,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_182])).

tff(c_188,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_77,c_185])).

tff(c_189,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_204,plain,(
    ! [A_71] :
      ( v1_compts_1(k1_pre_topc(A_71,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_71)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_189,c_189,c_38])).

tff(c_207,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_204])).

tff(c_210,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_77,c_207])).

tff(c_116,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_16])).

tff(c_119,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_116])).

tff(c_251,plain,(
    ! [A_84,B_85] :
      ( u1_struct_0(g1_pre_topc(A_84,B_85)) = A_84
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84)))
      | ~ v1_pre_topc(g1_pre_topc(A_84,B_85))
      | ~ l1_pre_topc(g1_pre_topc(A_84,B_85)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_126])).

tff(c_286,plain,(
    ! [A_91] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91))) = u1_struct_0(A_91)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_18,c_251])).

tff(c_294,plain,(
    ! [A_92] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92))) = u1_struct_0(A_92)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_69,c_286])).

tff(c_302,plain,(
    ! [A_93] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93))) = u1_struct_0(A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_75,c_294])).

tff(c_107,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_14])).

tff(c_113,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_107])).

tff(c_256,plain,(
    ! [A_86,B_87] :
      ( k2_struct_0(k1_pre_topc(A_86,B_87)) = B_87
      | ~ m1_pre_topc(k1_pre_topc(A_86,B_87),A_86)
      | ~ v1_pre_topc(k1_pre_topc(A_86,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_261,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_256])).

tff(c_265,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101,c_113,c_261])).

tff(c_269,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_4])).

tff(c_273,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_265,c_269])).

tff(c_369,plain,(
    ! [A_94] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_273])).

tff(c_376,plain,(
    ! [B_26] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_369])).

tff(c_2133,plain,(
    ! [B_152] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_152),u1_pre_topc(B_152)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_152)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_152),u1_pre_topc(B_152)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_152)
      | ~ l1_pre_topc(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_376])).

tff(c_2159,plain,(
    ! [A_153] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_75,c_2133])).

tff(c_191,plain,(
    ! [A_27] :
      ( v2_compts_1('#skF_3',A_27)
      | ~ v1_compts_1(k1_pre_topc(A_27,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_189,c_189,c_36])).

tff(c_327,plain,(
    ! [A_93] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93)),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_191])).

tff(c_2165,plain,(
    ! [A_153] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)))
      | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2159,c_327])).

tff(c_2220,plain,(
    ! [A_154] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_154),u1_pre_topc(A_154)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_154),u1_pre_topc(A_154)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_2165])).

tff(c_140,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2223,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2220,c_140])).

tff(c_2247,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_110,c_101,c_2223])).

tff(c_2284,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_2247])).

tff(c_2290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2284])).

tff(c_2292,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2291,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2322,plain,(
    ! [A_167,B_168] :
      ( u1_struct_0(g1_pre_topc(A_167,B_168)) = A_167
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k1_zfmisc_1(A_167)))
      | ~ v1_pre_topc(g1_pre_topc(A_167,B_168))
      | ~ l1_pre_topc(g1_pre_topc(A_167,B_168)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_126])).

tff(c_2362,plain,(
    ! [A_173] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_173),u1_pre_topc(A_173))) = u1_struct_0(A_173)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_173),u1_pre_topc(A_173)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_173),u1_pre_topc(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(resolution,[status(thm)],[c_18,c_2322])).

tff(c_2421,plain,(
    ! [A_176] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_176),u1_pre_topc(A_176))) = u1_struct_0(A_176)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_176),u1_pre_topc(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(resolution,[status(thm)],[c_69,c_2362])).

tff(c_2432,plain,(
    ! [A_177] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177))) = u1_struct_0(A_177)
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_75,c_2421])).

tff(c_2327,plain,(
    ! [A_169,B_170] :
      ( k2_struct_0(k1_pre_topc(A_169,B_170)) = B_170
      | ~ m1_pre_topc(k1_pre_topc(A_169,B_170),A_169)
      | ~ v1_pre_topc(k1_pre_topc(A_169,B_170))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2332,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_2327])).

tff(c_2336,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101,c_113,c_2332])).

tff(c_2340,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2336,c_4])).

tff(c_2344,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2336,c_2340])).

tff(c_2542,plain,(
    ! [A_182] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_182),u1_pre_topc(A_182)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0(A_182),u1_pre_topc(A_182)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_182),u1_pre_topc(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2432,c_2344])).

tff(c_2552,plain,(
    ! [B_26] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_26)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_2542])).

tff(c_4237,plain,(
    ! [B_238] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(B_238),u1_pre_topc(B_238)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(B_238)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_238),u1_pre_topc(B_238)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_238)
      | ~ l1_pre_topc(B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2552])).

tff(c_4262,plain,(
    ! [A_16] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_75,c_4237])).

tff(c_5963,plain,(
    ! [B_270,A_271] :
      ( v2_compts_1(B_270,g1_pre_topc(u1_struct_0(A_271),u1_pre_topc(A_271)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_271),u1_pre_topc(A_271)),B_270))
      | k1_xboole_0 = B_270
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_271),u1_pre_topc(A_271)))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_271),u1_pre_topc(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2432,c_32])).

tff(c_5975,plain,(
    ! [A_16] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
      | k1_xboole_0 = '#skF_3'
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4262,c_5963])).

tff(c_6001,plain,(
    ! [A_16] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | k1_xboole_0 = '#skF_3'
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2291,c_5975])).

tff(c_6005,plain,(
    ! [A_272] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_272),u1_pre_topc(A_272)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_272),u1_pre_topc(A_272)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_272),u1_pre_topc(A_272)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_272)
      | ~ l1_pre_topc(A_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2292,c_6001])).

tff(c_6008,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6005,c_140])).

tff(c_6038,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_110,c_101,c_6008])).

tff(c_6118,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6038])).

tff(c_6124,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_6118])).

tff(c_6130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6124])).

tff(c_6131,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6038])).

tff(c_6140,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_6131])).

tff(c_6147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6140])).

tff(c_6148,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6172,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_6148])).

tff(c_6355,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6324,c_6172])).

tff(c_6394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101,c_6355])).

tff(c_6396,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_6148])).

tff(c_6412,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6396,c_14])).

tff(c_6416,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6412])).

tff(c_6422,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_6416])).

tff(c_6428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6422])).

tff(c_6430,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6412])).

tff(c_6149,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7380,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6149,c_6396,c_48])).

tff(c_7388,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7380,c_12])).

tff(c_7403,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_7388])).

tff(c_7421,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7403,c_16])).

tff(c_7436,plain,(
    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_7421])).

tff(c_28,plain,(
    ! [A_24,B_26] :
      ( m1_pre_topc(A_24,B_26)
      | ~ m1_pre_topc(A_24,g1_pre_topc(u1_struct_0(B_26),u1_pre_topc(B_26)))
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7418,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_7403,c_28])).

tff(c_7433,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7418])).

tff(c_7493,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7436,c_7433])).

tff(c_7391,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7380,c_14])).

tff(c_7406,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_7391])).

tff(c_6,plain,(
    ! [A_2,B_6] :
      ( k2_struct_0(k1_pre_topc(A_2,B_6)) = B_6
      | ~ m1_pre_topc(k1_pre_topc(A_2,B_6),A_2)
      | ~ v1_pre_topc(k1_pre_topc(A_2,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7415,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7403,c_6])).

tff(c_7430,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_7380,c_7406,c_7415])).

tff(c_7467,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_2)
      | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7430,c_4])).

tff(c_7842,plain,(
    ! [A_375] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc(A_375,'#skF_2')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_375)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7406,c_7430,c_7467])).

tff(c_7845,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7493,c_7842])).

tff(c_7858,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7845])).

tff(c_8033,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7858])).

tff(c_128,plain,(
    ! [A_1,C_46,D_48] :
      ( u1_struct_0(A_1) = C_46
      | g1_pre_topc(C_46,D_48) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_7808,plain,(
    ! [C_373,D_374] :
      ( u1_struct_0(g1_pre_topc(C_373,D_374)) = C_373
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_373,D_374)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_373,D_374)))))
      | ~ v1_pre_topc(g1_pre_topc(C_373,D_374))
      | ~ l1_pre_topc(g1_pre_topc(C_373,D_374)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_128])).

tff(c_7954,plain,(
    ! [C_376,D_377] :
      ( u1_struct_0(g1_pre_topc(C_376,D_377)) = C_376
      | ~ v1_pre_topc(g1_pre_topc(C_376,D_377))
      | ~ l1_pre_topc(g1_pre_topc(C_376,D_377)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7808])).

tff(c_8049,plain,(
    ! [A_382] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_382),u1_pre_topc(A_382))) = u1_struct_0(A_382)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_382),u1_pre_topc(A_382)))
      | ~ l1_pre_topc(A_382) ) ),
    inference(resolution,[status(thm)],[c_69,c_7954])).

tff(c_8061,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6430,c_8049])).

tff(c_8074,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8061])).

tff(c_8085,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8074,c_7380])).

tff(c_8093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8033,c_8085])).

tff(c_8095,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7858])).

tff(c_8101,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8095,c_32])).

tff(c_8112,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_8101])).

tff(c_8113,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_8112])).

tff(c_8164,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8113])).

tff(c_8094,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_7858])).

tff(c_6395,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6148])).

tff(c_34,plain,(
    ! [A_27,B_29] :
      ( v1_compts_1(k1_pre_topc(A_27,B_29))
      | ~ v2_compts_1(B_29,A_27)
      | k1_xboole_0 = B_29
      | ~ v2_pre_topc(A_27)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7383,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7380,c_34])).

tff(c_7397,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6395,c_7383])).

tff(c_7446,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7397])).

tff(c_7449,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_7446])).

tff(c_7456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_7449])).

tff(c_7457,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7397])).

tff(c_7478,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7457])).

tff(c_8176,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8094,c_7478])).

tff(c_8183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8164,c_8176])).

tff(c_8185,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_8113])).

tff(c_8184,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8113])).

tff(c_8264,plain,(
    ! [A_386] :
      ( v2_compts_1('#skF_2',A_386)
      | ~ v1_compts_1(k1_pre_topc(A_386,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8184,c_8184,c_8184,c_36])).

tff(c_8267,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8095,c_8264])).

tff(c_8273,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8185,c_8267])).

tff(c_8275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_8273])).

tff(c_8277,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7457])).

tff(c_8276,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7457])).

tff(c_8292,plain,(
    ! [A_387] :
      ( v1_compts_1(k1_pre_topc(A_387,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_387)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8276,c_8276,c_8276,c_38])).

tff(c_8295,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7380,c_8292])).

tff(c_8298,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6395,c_8295])).

tff(c_8300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8277,c_8298])).

tff(c_8302,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14390,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14383,c_8302,c_46])).

tff(c_14391,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_14390])).

tff(c_14558,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14531,c_14391])).

tff(c_14597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101,c_14558])).

tff(c_14598,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14390])).

tff(c_14599,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_14390])).

tff(c_14609,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14599,c_14])).

tff(c_14612,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14609])).

tff(c_14618,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_14612])).

tff(c_14624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14618])).

tff(c_14626,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14609])).

tff(c_14992,plain,(
    ! [A_681,B_682] :
      ( u1_struct_0(g1_pre_topc(A_681,B_682)) = A_681
      | ~ m1_subset_1(B_682,k1_zfmisc_1(k1_zfmisc_1(A_681)))
      | ~ v1_pre_topc(g1_pre_topc(A_681,B_682))
      | ~ l1_pre_topc(g1_pre_topc(A_681,B_682)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8337])).

tff(c_15066,plain,(
    ! [A_684] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_684),u1_pre_topc(A_684))) = u1_struct_0(A_684)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_684),u1_pre_topc(A_684)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_684),u1_pre_topc(A_684)))
      | ~ l1_pre_topc(A_684) ) ),
    inference(resolution,[status(thm)],[c_18,c_14992])).

tff(c_15074,plain,(
    ! [A_685] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_685),u1_pre_topc(A_685))) = u1_struct_0(A_685)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_685),u1_pre_topc(A_685)))
      | ~ l1_pre_topc(A_685) ) ),
    inference(resolution,[status(thm)],[c_69,c_15066])).

tff(c_15077,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14626,c_15074])).

tff(c_15086,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_15077])).

tff(c_14628,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14383,c_14599,c_48])).

tff(c_15101,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15086,c_14628])).

tff(c_15104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14598,c_15101])).

tff(c_15106,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_15112,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_15106,c_52])).

tff(c_15113,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_15112])).

tff(c_54,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_15151,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_15106,c_54])).

tff(c_15161,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15151,c_14])).

tff(c_15165,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15161])).

tff(c_15171,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_15165])).

tff(c_15177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_15171])).

tff(c_15179,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15161])).

tff(c_15119,plain,(
    ! [C_688,A_689,D_690,B_691] :
      ( C_688 = A_689
      | g1_pre_topc(C_688,D_690) != g1_pre_topc(A_689,B_691)
      | ~ m1_subset_1(B_691,k1_zfmisc_1(k1_zfmisc_1(A_689))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15121,plain,(
    ! [A_1,A_689,B_691] :
      ( u1_struct_0(A_1) = A_689
      | g1_pre_topc(A_689,B_691) != A_1
      | ~ m1_subset_1(B_691,k1_zfmisc_1(k1_zfmisc_1(A_689)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15119])).

tff(c_15270,plain,(
    ! [A_722,B_723] :
      ( u1_struct_0(g1_pre_topc(A_722,B_723)) = A_722
      | ~ m1_subset_1(B_723,k1_zfmisc_1(k1_zfmisc_1(A_722)))
      | ~ v1_pre_topc(g1_pre_topc(A_722,B_723))
      | ~ l1_pre_topc(g1_pre_topc(A_722,B_723)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15121])).

tff(c_15350,plain,(
    ! [A_728] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_728),u1_pre_topc(A_728))) = u1_struct_0(A_728)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_728),u1_pre_topc(A_728)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_728),u1_pre_topc(A_728)))
      | ~ l1_pre_topc(A_728) ) ),
    inference(resolution,[status(thm)],[c_18,c_15270])).

tff(c_15358,plain,(
    ! [A_729] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_729),u1_pre_topc(A_729))) = u1_struct_0(A_729)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_729),u1_pre_topc(A_729)))
      | ~ l1_pre_topc(A_729) ) ),
    inference(resolution,[status(thm)],[c_69,c_15350])).

tff(c_15361,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15179,c_15358])).

tff(c_15370,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_15361])).

tff(c_15372,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15370,c_15151])).

tff(c_15469,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15372,c_32])).

tff(c_15480,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_15469])).

tff(c_15481,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_15113,c_15480])).

tff(c_15508,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_15481])).

tff(c_15160,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15151,c_12])).

tff(c_15282,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15179,c_15160])).

tff(c_15290,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15282,c_16])).

tff(c_15305,plain,(
    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15179,c_15290])).

tff(c_15287,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_15282,c_28])).

tff(c_15302,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_15287])).

tff(c_15330,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15305,c_15302])).

tff(c_15178,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_15161])).

tff(c_15284,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15282,c_6])).

tff(c_15299,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15179,c_15151,c_15178,c_15284])).

tff(c_15318,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_2)
      | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15299,c_4])).

tff(c_16197,plain,(
    ! [A_748] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc(A_748,'#skF_2')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_748)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_748)))
      | ~ l1_pre_topc(A_748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15178,c_15299,c_15318])).

tff(c_16204,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15330,c_16197])).

tff(c_16221,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_15372,c_16204])).

tff(c_15105,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_15216,plain,(
    ! [A_712,B_713] :
      ( v1_compts_1(k1_pre_topc(A_712,B_713))
      | ~ v2_compts_1(B_713,A_712)
      | k1_xboole_0 = B_713
      | ~ v2_pre_topc(A_712)
      | ~ m1_subset_1(B_713,k1_zfmisc_1(u1_struct_0(A_712)))
      | ~ l1_pre_topc(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_15219,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15151,c_15216])).

tff(c_15222,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15179,c_15105,c_15219])).

tff(c_15223,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15222])).

tff(c_15226,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_15223])).

tff(c_15233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_15226])).

tff(c_15234,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_15222])).

tff(c_15241,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_15234])).

tff(c_16236,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16221,c_15241])).

tff(c_16242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15508,c_16236])).

tff(c_16244,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_15481])).

tff(c_16243,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15481])).

tff(c_16530,plain,(
    ! [A_758] :
      ( v2_compts_1('#skF_2',A_758)
      | ~ v1_compts_1(k1_pre_topc(A_758,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_758)))
      | ~ l1_pre_topc(A_758) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16243,c_16243,c_16243,c_36])).

tff(c_16539,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15372,c_16530])).

tff(c_16547,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16244,c_16539])).

tff(c_16549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15113,c_16547])).

tff(c_16551,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_15234])).

tff(c_16550,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15234])).

tff(c_16570,plain,(
    ! [A_761] :
      ( v1_compts_1(k1_pre_topc(A_761,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_761)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_761)))
      | ~ l1_pre_topc(A_761) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16550,c_16550,c_16550,c_38])).

tff(c_16573,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15151,c_16570])).

tff(c_16576,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15179,c_15105,c_16573])).

tff(c_16578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16551,c_16576])).

tff(c_16579,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15112])).

tff(c_16581,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_15106,c_54])).

tff(c_16591,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16581,c_14])).

tff(c_16632,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_16591])).

tff(c_16639,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_16632])).

tff(c_16645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16639])).

tff(c_16647,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16591])).

tff(c_16600,plain,(
    ! [D_762,B_763,C_764,A_765] :
      ( D_762 = B_763
      | g1_pre_topc(C_764,D_762) != g1_pre_topc(A_765,B_763)
      | ~ m1_subset_1(B_763,k1_zfmisc_1(k1_zfmisc_1(A_765))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16602,plain,(
    ! [A_1,B_763,A_765] :
      ( u1_pre_topc(A_1) = B_763
      | g1_pre_topc(A_765,B_763) != A_1
      | ~ m1_subset_1(B_763,k1_zfmisc_1(k1_zfmisc_1(A_765)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16600])).

tff(c_16739,plain,(
    ! [A_796,B_797] :
      ( u1_pre_topc(g1_pre_topc(A_796,B_797)) = B_797
      | ~ m1_subset_1(B_797,k1_zfmisc_1(k1_zfmisc_1(A_796)))
      | ~ v1_pre_topc(g1_pre_topc(A_796,B_797))
      | ~ l1_pre_topc(g1_pre_topc(A_796,B_797)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16602])).

tff(c_16811,plain,(
    ! [A_800] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_800),u1_pre_topc(A_800))) = u1_pre_topc(A_800)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_800),u1_pre_topc(A_800)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_800),u1_pre_topc(A_800)))
      | ~ l1_pre_topc(A_800) ) ),
    inference(resolution,[status(thm)],[c_18,c_16739])).

tff(c_16821,plain,(
    ! [A_801] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_801),u1_pre_topc(A_801))) = u1_pre_topc(A_801)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_801),u1_pre_topc(A_801)))
      | ~ l1_pre_topc(A_801) ) ),
    inference(resolution,[status(thm)],[c_69,c_16811])).

tff(c_16824,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16647,c_16821])).

tff(c_16833,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16824])).

tff(c_16850,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16833,c_2])).

tff(c_16874,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16647,c_16850])).

tff(c_17333,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_16874])).

tff(c_17339,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_17333])).

tff(c_17345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17339])).

tff(c_17347,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16874])).

tff(c_16859,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16833,c_18])).

tff(c_16880,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16647,c_16859])).

tff(c_16609,plain,(
    ! [C_766,A_767,D_768,B_769] :
      ( C_766 = A_767
      | g1_pre_topc(C_766,D_768) != g1_pre_topc(A_767,B_769)
      | ~ m1_subset_1(B_769,k1_zfmisc_1(k1_zfmisc_1(A_767))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16613,plain,(
    ! [A_1,C_766,D_768] :
      ( u1_struct_0(A_1) = C_766
      | g1_pre_topc(C_766,D_768) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16609])).

tff(c_17442,plain,(
    ! [C_814,D_815] :
      ( u1_struct_0(g1_pre_topc(C_814,D_815)) = C_814
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_814,D_815)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_814,D_815)))))
      | ~ v1_pre_topc(g1_pre_topc(C_814,D_815))
      | ~ l1_pre_topc(g1_pre_topc(C_814,D_815)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16613])).

tff(c_17454,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16833,c_17442])).

tff(c_17469,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16647,c_17347,c_16880,c_17454])).

tff(c_17473,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17469,c_16581])).

tff(c_17475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16579,c_17473])).

tff(c_17477,plain,(
    ~ v2_compts_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_17478,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_17477,c_58])).

tff(c_17479,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_17478])).

tff(c_60,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_17508,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_17477,c_60])).

tff(c_17518,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17508,c_14])).

tff(c_17558,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_17518])).

tff(c_17564,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_17558])).

tff(c_17570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17564])).

tff(c_17572,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_17518])).

tff(c_17534,plain,(
    ! [D_826,B_827,C_828,A_829] :
      ( D_826 = B_827
      | g1_pre_topc(C_828,D_826) != g1_pre_topc(A_829,B_827)
      | ~ m1_subset_1(B_827,k1_zfmisc_1(k1_zfmisc_1(A_829))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_17536,plain,(
    ! [A_1,B_827,A_829] :
      ( u1_pre_topc(A_1) = B_827
      | g1_pre_topc(A_829,B_827) != A_1
      | ~ m1_subset_1(B_827,k1_zfmisc_1(k1_zfmisc_1(A_829)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17534])).

tff(c_17669,plain,(
    ! [A_858,B_859] :
      ( u1_pre_topc(g1_pre_topc(A_858,B_859)) = B_859
      | ~ m1_subset_1(B_859,k1_zfmisc_1(k1_zfmisc_1(A_858)))
      | ~ v1_pre_topc(g1_pre_topc(A_858,B_859))
      | ~ l1_pre_topc(g1_pre_topc(A_858,B_859)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17536])).

tff(c_17736,plain,(
    ! [A_860] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_860),u1_pre_topc(A_860))) = u1_pre_topc(A_860)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_860),u1_pre_topc(A_860)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_860),u1_pre_topc(A_860)))
      | ~ l1_pre_topc(A_860) ) ),
    inference(resolution,[status(thm)],[c_18,c_17669])).

tff(c_17744,plain,(
    ! [A_861] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_861),u1_pre_topc(A_861))) = u1_pre_topc(A_861)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_861),u1_pre_topc(A_861)))
      | ~ l1_pre_topc(A_861) ) ),
    inference(resolution,[status(thm)],[c_69,c_17736])).

tff(c_17747,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17572,c_17744])).

tff(c_17756,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17747])).

tff(c_17792,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17756,c_18])).

tff(c_17815,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17792])).

tff(c_17525,plain,(
    ! [C_822,A_823,D_824,B_825] :
      ( C_822 = A_823
      | g1_pre_topc(C_822,D_824) != g1_pre_topc(A_823,B_825)
      | ~ m1_subset_1(B_825,k1_zfmisc_1(k1_zfmisc_1(A_823))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_17529,plain,(
    ! [A_1,C_822,D_824] :
      ( u1_struct_0(A_1) = C_822
      | g1_pre_topc(C_822,D_824) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17525])).

tff(c_17979,plain,(
    ! [C_865,D_866] :
      ( u1_struct_0(g1_pre_topc(C_865,D_866)) = C_865
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_865,D_866)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_865,D_866)))))
      | ~ v1_pre_topc(g1_pre_topc(C_865,D_866))
      | ~ l1_pre_topc(g1_pre_topc(C_865,D_866)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17529])).

tff(c_17988,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17756,c_17979])).

tff(c_18001,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17815,c_17988])).

tff(c_18021,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_18001])).

tff(c_18027,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_18021])).

tff(c_18033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18027])).

tff(c_18034,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18001])).

tff(c_18072,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18034,c_17508])).

tff(c_18198,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18072,c_32])).

tff(c_18209,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_18198])).

tff(c_18210,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17479,c_18209])).

tff(c_18228,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18210])).

tff(c_17517,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17508,c_12])).

tff(c_17675,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17517])).

tff(c_17683,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17675,c_16])).

tff(c_17698,plain,(
    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17683])).

tff(c_17680,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_17675,c_28])).

tff(c_17695,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_17680])).

tff(c_17724,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17698,c_17695])).

tff(c_17571,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17518])).

tff(c_17677,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17675,c_6])).

tff(c_17692,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17508,c_17571,c_17677])).

tff(c_17712,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_2)
      | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17692,c_4])).

tff(c_18523,plain,(
    ! [A_880] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc(A_880,'#skF_2')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_880)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_880)))
      | ~ l1_pre_topc(A_880) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17571,c_17692,c_17712])).

tff(c_18526,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17724,c_18523])).

tff(c_18539,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18072,c_18526])).

tff(c_17476,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_17610,plain,(
    ! [A_846,B_847] :
      ( v1_compts_1(k1_pre_topc(A_846,B_847))
      | ~ v2_compts_1(B_847,A_846)
      | k1_xboole_0 = B_847
      | ~ v2_pre_topc(A_846)
      | ~ m1_subset_1(B_847,k1_zfmisc_1(u1_struct_0(A_846)))
      | ~ l1_pre_topc(A_846) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_17613,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17508,c_17610])).

tff(c_17616,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17476,c_17613])).

tff(c_17617,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_17616])).

tff(c_17620,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_17617])).

tff(c_17627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_17620])).

tff(c_17628,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17616])).

tff(c_17635,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17628])).

tff(c_18554,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18539,c_17635])).

tff(c_18560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18228,c_18554])).

tff(c_18562,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18210])).

tff(c_18561,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18210])).

tff(c_18662,plain,(
    ! [A_887] :
      ( v2_compts_1('#skF_2',A_887)
      | ~ v1_compts_1(k1_pre_topc(A_887,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_887)))
      | ~ l1_pre_topc(A_887) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18561,c_18561,c_18561,c_36])).

tff(c_18665,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18072,c_18662])).

tff(c_18671,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18562,c_18665])).

tff(c_18673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17479,c_18671])).

tff(c_18675,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17628])).

tff(c_18674,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17628])).

tff(c_18701,plain,(
    ! [A_891] :
      ( v1_compts_1(k1_pre_topc(A_891,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_891)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_891)))
      | ~ l1_pre_topc(A_891) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_18674,c_18674,c_38])).

tff(c_18704,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17508,c_18701])).

tff(c_18707,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17572,c_17476,c_18704])).

tff(c_18709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18675,c_18707])).

tff(c_18710,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_17478])).

tff(c_18712,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_17477,c_60])).

tff(c_18743,plain,(
    ! [A_894,B_895] :
      ( v1_pre_topc(k1_pre_topc(A_894,B_895))
      | ~ m1_subset_1(B_895,k1_zfmisc_1(u1_struct_0(A_894)))
      | ~ l1_pre_topc(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18747,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18712,c_18743])).

tff(c_18792,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_18747])).

tff(c_18798,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_18792])).

tff(c_18804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18798])).

tff(c_18806,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_18747])).

tff(c_18769,plain,(
    ! [C_902,A_903,D_904,B_905] :
      ( C_902 = A_903
      | g1_pre_topc(C_902,D_904) != g1_pre_topc(A_903,B_905)
      | ~ m1_subset_1(B_905,k1_zfmisc_1(k1_zfmisc_1(A_903))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18771,plain,(
    ! [A_1,A_903,B_905] :
      ( u1_struct_0(A_1) = A_903
      | g1_pre_topc(A_903,B_905) != A_1
      | ~ m1_subset_1(B_905,k1_zfmisc_1(k1_zfmisc_1(A_903)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18769])).

tff(c_18897,plain,(
    ! [A_930,B_931] :
      ( u1_struct_0(g1_pre_topc(A_930,B_931)) = A_930
      | ~ m1_subset_1(B_931,k1_zfmisc_1(k1_zfmisc_1(A_930)))
      | ~ v1_pre_topc(g1_pre_topc(A_930,B_931))
      | ~ l1_pre_topc(g1_pre_topc(A_930,B_931)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18771])).

tff(c_18974,plain,(
    ! [A_936] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_936),u1_pre_topc(A_936))) = u1_struct_0(A_936)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_936),u1_pre_topc(A_936)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_936),u1_pre_topc(A_936)))
      | ~ l1_pre_topc(A_936) ) ),
    inference(resolution,[status(thm)],[c_18,c_18897])).

tff(c_18982,plain,(
    ! [A_937] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_937),u1_pre_topc(A_937))) = u1_struct_0(A_937)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_937),u1_pre_topc(A_937)))
      | ~ l1_pre_topc(A_937) ) ),
    inference(resolution,[status(thm)],[c_69,c_18974])).

tff(c_18985,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18806,c_18982])).

tff(c_18994,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18985])).

tff(c_18996,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18994,c_18712])).

tff(c_18998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18710,c_18996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:25:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.77/4.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.07/4.65  
% 12.07/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.07/4.66  %$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.07/4.66  
% 12.07/4.66  %Foreground sorts:
% 12.07/4.66  
% 12.07/4.66  
% 12.07/4.66  %Background operators:
% 12.07/4.66  
% 12.07/4.66  
% 12.07/4.66  %Foreground operators:
% 12.07/4.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.07/4.66  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 12.07/4.66  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 12.07/4.66  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.07/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.07/4.66  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.07/4.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.07/4.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.07/4.66  tff('#skF_2', type, '#skF_2': $i).
% 12.07/4.66  tff('#skF_3', type, '#skF_3': $i).
% 12.07/4.66  tff('#skF_1', type, '#skF_1': $i).
% 12.07/4.66  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 12.07/4.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.07/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.07/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.07/4.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.07/4.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.07/4.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.07/4.66  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 12.07/4.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.07/4.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.07/4.66  
% 12.35/4.70  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_compts_1(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v2_compts_1(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_compts_1)).
% 12.35/4.70  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 12.35/4.70  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 12.35/4.70  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 12.35/4.70  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 12.35/4.70  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 12.35/4.70  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 12.35/4.70  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 12.35/4.70  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.35/4.70  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 12.35/4.70  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 12.35/4.70  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.70  tff(c_56, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.70  tff(c_101, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_56])).
% 12.35/4.70  tff(c_18, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.35/4.70  tff(c_71, plain, (![A_37, B_38]: (l1_pre_topc(g1_pre_topc(A_37, B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.35/4.70  tff(c_75, plain, (![A_16]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_71])).
% 12.35/4.70  tff(c_65, plain, (![A_34, B_35]: (v1_pre_topc(g1_pre_topc(A_34, B_35)) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.35/4.70  tff(c_69, plain, (![A_16]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_65])).
% 12.35/4.70  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.35/4.70  tff(c_8335, plain, (![C_392, A_393, D_394, B_395]: (C_392=A_393 | g1_pre_topc(C_392, D_394)!=g1_pre_topc(A_393, B_395) | ~m1_subset_1(B_395, k1_zfmisc_1(k1_zfmisc_1(A_393))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.70  tff(c_8337, plain, (![A_1, A_393, B_395]: (u1_struct_0(A_1)=A_393 | g1_pre_topc(A_393, B_395)!=A_1 | ~m1_subset_1(B_395, k1_zfmisc_1(k1_zfmisc_1(A_393))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8335])).
% 12.35/4.70  tff(c_14505, plain, (![A_646, B_647]: (u1_struct_0(g1_pre_topc(A_646, B_647))=A_646 | ~m1_subset_1(B_647, k1_zfmisc_1(k1_zfmisc_1(A_646))) | ~v1_pre_topc(g1_pre_topc(A_646, B_647)) | ~l1_pre_topc(g1_pre_topc(A_646, B_647)))), inference(reflexivity, [status(thm), theory('equality')], [c_8337])).
% 12.35/4.70  tff(c_14515, plain, (![A_650]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_650), u1_pre_topc(A_650)))=u1_struct_0(A_650) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_650), u1_pre_topc(A_650))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_650), u1_pre_topc(A_650))) | ~l1_pre_topc(A_650))), inference(resolution, [status(thm)], [c_18, c_14505])).
% 12.35/4.70  tff(c_14523, plain, (![A_651]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_651), u1_pre_topc(A_651)))=u1_struct_0(A_651) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_651), u1_pre_topc(A_651))) | ~l1_pre_topc(A_651))), inference(resolution, [status(thm)], [c_69, c_14515])).
% 12.35/4.70  tff(c_14531, plain, (![A_652]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_652), u1_pre_topc(A_652)))=u1_struct_0(A_652) | ~l1_pre_topc(A_652))), inference(resolution, [status(thm)], [c_75, c_14523])).
% 12.35/4.70  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.70  tff(c_20, plain, (![A_17]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17))) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.35/4.70  tff(c_12, plain, (![A_11, B_12]: (m1_pre_topc(k1_pre_topc(A_11, B_12), A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.35/4.70  tff(c_8304, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_12])).
% 12.35/4.70  tff(c_8310, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8304])).
% 12.35/4.70  tff(c_62, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.70  tff(c_77, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 12.35/4.70  tff(c_8382, plain, (![A_408, B_409]: (v1_compts_1(k1_pre_topc(A_408, B_409)) | ~v2_compts_1(B_409, A_408) | k1_xboole_0=B_409 | ~v2_pre_topc(A_408) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | ~l1_pre_topc(A_408))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.70  tff(c_8385, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_8382])).
% 12.35/4.70  tff(c_8388, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_77, c_8385])).
% 12.35/4.70  tff(c_8396, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_8388])).
% 12.35/4.70  tff(c_38, plain, (![A_27]: (v1_compts_1(k1_pre_topc(A_27, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_27) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.70  tff(c_8405, plain, (![A_412]: (v1_compts_1(k1_pre_topc(A_412, '#skF_3')) | ~v2_compts_1('#skF_3', A_412) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_412))) | ~l1_pre_topc(A_412))), inference(demodulation, [status(thm), theory('equality')], [c_8396, c_8396, c_8396, c_38])).
% 12.35/4.70  tff(c_8408, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_8405])).
% 12.35/4.70  tff(c_8411, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_77, c_8408])).
% 12.35/4.70  tff(c_16, plain, (![B_15, A_13]: (l1_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.35/4.70  tff(c_8317, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8310, c_16])).
% 12.35/4.70  tff(c_8320, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8317])).
% 12.35/4.70  tff(c_30, plain, (![A_24, B_26]: (m1_pre_topc(A_24, g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(A_24, B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.35/4.70  tff(c_8480, plain, (![A_430, B_431]: (u1_struct_0(g1_pre_topc(A_430, B_431))=A_430 | ~m1_subset_1(B_431, k1_zfmisc_1(k1_zfmisc_1(A_430))) | ~v1_pre_topc(g1_pre_topc(A_430, B_431)) | ~l1_pre_topc(g1_pre_topc(A_430, B_431)))), inference(reflexivity, [status(thm), theory('equality')], [c_8337])).
% 12.35/4.70  tff(c_8493, plain, (![A_433]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_433), u1_pre_topc(A_433)))=u1_struct_0(A_433) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_433), u1_pre_topc(A_433))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_433), u1_pre_topc(A_433))) | ~l1_pre_topc(A_433))), inference(resolution, [status(thm)], [c_18, c_8480])).
% 12.35/4.70  tff(c_8501, plain, (![A_434]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_434), u1_pre_topc(A_434)))=u1_struct_0(A_434) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_434), u1_pre_topc(A_434))) | ~l1_pre_topc(A_434))), inference(resolution, [status(thm)], [c_69, c_8493])).
% 12.35/4.70  tff(c_8512, plain, (![A_437]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_437), u1_pre_topc(A_437)))=u1_struct_0(A_437) | ~l1_pre_topc(A_437))), inference(resolution, [status(thm)], [c_75, c_8501])).
% 12.35/4.70  tff(c_14, plain, (![A_11, B_12]: (v1_pre_topc(k1_pre_topc(A_11, B_12)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.35/4.70  tff(c_8307, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_14])).
% 12.35/4.70  tff(c_8313, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8307])).
% 12.35/4.70  tff(c_8440, plain, (![A_422, B_423]: (k2_struct_0(k1_pre_topc(A_422, B_423))=B_423 | ~m1_pre_topc(k1_pre_topc(A_422, B_423), A_422) | ~v1_pre_topc(k1_pre_topc(A_422, B_423)) | ~m1_subset_1(B_423, k1_zfmisc_1(u1_struct_0(A_422))) | ~l1_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.35/4.70  tff(c_8445, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8310, c_8440])).
% 12.35/4.70  tff(c_8449, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101, c_8313, c_8445])).
% 12.35/4.70  tff(c_4, plain, (![A_2, C_8]: (k1_pre_topc(A_2, k2_struct_0(C_8))=C_8 | ~m1_pre_topc(C_8, A_2) | ~v1_pre_topc(C_8) | ~m1_subset_1(k2_struct_0(C_8), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.35/4.70  tff(c_8453, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_8449, c_4])).
% 12.35/4.70  tff(c_8457, plain, (![A_2]: (k1_pre_topc(A_2, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_8313, c_8449, c_8453])).
% 12.35/4.70  tff(c_8589, plain, (![A_439]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_439), u1_pre_topc(A_439)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0(A_439), u1_pre_topc(A_439))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_439))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_439), u1_pre_topc(A_439))) | ~l1_pre_topc(A_439))), inference(superposition, [status(thm), theory('equality')], [c_8512, c_8457])).
% 12.35/4.70  tff(c_8596, plain, (![B_26]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_26))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_8589])).
% 12.35/4.70  tff(c_10444, plain, (![B_501]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_501), u1_pre_topc(B_501)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_501))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_501), u1_pre_topc(B_501))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_501) | ~l1_pre_topc(B_501))), inference(demodulation, [status(thm), theory('equality')], [c_8320, c_8596])).
% 12.35/4.70  tff(c_10470, plain, (![A_502]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_502), u1_pre_topc(A_502)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_502) | ~l1_pre_topc(A_502))), inference(resolution, [status(thm)], [c_75, c_10444])).
% 12.35/4.70  tff(c_36, plain, (![A_27]: (v2_compts_1(k1_xboole_0, A_27) | ~v1_compts_1(k1_pre_topc(A_27, k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.70  tff(c_8400, plain, (![A_27]: (v2_compts_1('#skF_3', A_27) | ~v1_compts_1(k1_pre_topc(A_27, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_8396, c_8396, c_8396, c_36])).
% 12.35/4.70  tff(c_8537, plain, (![A_437]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_437), u1_pre_topc(A_437))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_437), u1_pre_topc(A_437)), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_437))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_437), u1_pre_topc(A_437))) | ~l1_pre_topc(A_437))), inference(superposition, [status(thm), theory('equality')], [c_8512, c_8400])).
% 12.35/4.70  tff(c_10483, plain, (![A_502]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_502), u1_pre_topc(A_502))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_502))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_502), u1_pre_topc(A_502))) | ~l1_pre_topc(A_502) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_502) | ~l1_pre_topc(A_502))), inference(superposition, [status(thm), theory('equality')], [c_10470, c_8537])).
% 12.35/4.70  tff(c_10540, plain, (![A_503]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_503), u1_pre_topc(A_503))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_503), u1_pre_topc(A_503))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_503))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_503) | ~l1_pre_topc(A_503))), inference(demodulation, [status(thm), theory('equality')], [c_8411, c_10483])).
% 12.35/4.70  tff(c_50, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.70  tff(c_8358, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_50])).
% 12.35/4.70  tff(c_10543, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10540, c_8358])).
% 12.35/4.70  tff(c_10567, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8310, c_101, c_10543])).
% 12.35/4.70  tff(c_10573, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_10567])).
% 12.35/4.70  tff(c_10579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_10573])).
% 12.35/4.70  tff(c_10581, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_8388])).
% 12.35/4.70  tff(c_10580, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_8388])).
% 12.35/4.70  tff(c_10601, plain, (![A_512, B_513]: (u1_struct_0(g1_pre_topc(A_512, B_513))=A_512 | ~m1_subset_1(B_513, k1_zfmisc_1(k1_zfmisc_1(A_512))) | ~v1_pre_topc(g1_pre_topc(A_512, B_513)) | ~l1_pre_topc(g1_pre_topc(A_512, B_513)))), inference(reflexivity, [status(thm), theory('equality')], [c_8337])).
% 12.35/4.70  tff(c_10740, plain, (![A_525]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_525), u1_pre_topc(A_525)))=u1_struct_0(A_525) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_525), u1_pre_topc(A_525))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_525), u1_pre_topc(A_525))) | ~l1_pre_topc(A_525))), inference(resolution, [status(thm)], [c_18, c_10601])).
% 12.35/4.70  tff(c_10751, plain, (![A_526]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_526), u1_pre_topc(A_526)))=u1_struct_0(A_526) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_526), u1_pre_topc(A_526))) | ~l1_pre_topc(A_526))), inference(resolution, [status(thm)], [c_69, c_10740])).
% 12.35/4.70  tff(c_10767, plain, (![A_529]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_529), u1_pre_topc(A_529)))=u1_struct_0(A_529) | ~l1_pre_topc(A_529))), inference(resolution, [status(thm)], [c_75, c_10751])).
% 12.35/4.70  tff(c_10611, plain, (![A_516, B_517]: (k2_struct_0(k1_pre_topc(A_516, B_517))=B_517 | ~m1_pre_topc(k1_pre_topc(A_516, B_517), A_516) | ~v1_pre_topc(k1_pre_topc(A_516, B_517)) | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0(A_516))) | ~l1_pre_topc(A_516))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.35/4.70  tff(c_10616, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8310, c_10611])).
% 12.35/4.70  tff(c_10620, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101, c_8313, c_10616])).
% 12.35/4.70  tff(c_10624, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_10620, c_4])).
% 12.35/4.70  tff(c_10628, plain, (![A_2]: (k1_pre_topc(A_2, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_8313, c_10620, c_10624])).
% 12.35/4.70  tff(c_10874, plain, (![A_531]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_531), u1_pre_topc(A_531)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0(A_531), u1_pre_topc(A_531))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_531))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_531), u1_pre_topc(A_531))) | ~l1_pre_topc(A_531))), inference(superposition, [status(thm), theory('equality')], [c_10767, c_10628])).
% 12.35/4.70  tff(c_10884, plain, (![B_26]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_26))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_10874])).
% 12.35/4.70  tff(c_12521, plain, (![B_585]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_585), u1_pre_topc(B_585)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_585))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_585), u1_pre_topc(B_585))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_585) | ~l1_pre_topc(B_585))), inference(demodulation, [status(thm), theory('equality')], [c_8320, c_10884])).
% 12.35/4.70  tff(c_12546, plain, (![A_16]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_75, c_12521])).
% 12.35/4.70  tff(c_32, plain, (![B_29, A_27]: (v2_compts_1(B_29, A_27) | ~v1_compts_1(k1_pre_topc(A_27, B_29)) | k1_xboole_0=B_29 | ~v2_pre_topc(A_27) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.70  tff(c_14197, plain, (![B_616, A_617]: (v2_compts_1(B_616, g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617)), B_616)) | k1_xboole_0=B_616 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617))) | ~m1_subset_1(B_616, k1_zfmisc_1(u1_struct_0(A_617))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_617), u1_pre_topc(A_617))) | ~l1_pre_topc(A_617))), inference(superposition, [status(thm), theory('equality')], [c_10767, c_32])).
% 12.35/4.70  tff(c_14209, plain, (![A_16]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_16) | ~l1_pre_topc(A_16))), inference(superposition, [status(thm), theory('equality')], [c_12546, c_14197])).
% 12.35/4.70  tff(c_14235, plain, (![A_16]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_16) | ~l1_pre_topc(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_10580, c_14209])).
% 12.35/4.70  tff(c_14239, plain, (![A_618]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_618), u1_pre_topc(A_618))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_618), u1_pre_topc(A_618))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_618), u1_pre_topc(A_618))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_618))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_618) | ~l1_pre_topc(A_618))), inference(negUnitSimplification, [status(thm)], [c_10581, c_14235])).
% 12.35/4.70  tff(c_14242, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14239, c_8358])).
% 12.35/4.70  tff(c_14272, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8310, c_101, c_14242])).
% 12.35/4.70  tff(c_14273, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_14272])).
% 12.35/4.70  tff(c_14279, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_14273])).
% 12.35/4.70  tff(c_14285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_14279])).
% 12.35/4.70  tff(c_14286, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_14272])).
% 12.35/4.70  tff(c_14374, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_14286])).
% 12.35/4.70  tff(c_14381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_14374])).
% 12.35/4.70  tff(c_14383, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 12.35/4.70  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.70  tff(c_102, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 12.35/4.70  tff(c_124, plain, (![C_46, A_47, D_48, B_49]: (C_46=A_47 | g1_pre_topc(C_46, D_48)!=g1_pre_topc(A_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.70  tff(c_126, plain, (![A_1, A_47, B_49]: (u1_struct_0(A_1)=A_47 | g1_pre_topc(A_47, B_49)!=A_1 | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_47))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 12.35/4.70  tff(c_6295, plain, (![A_310, B_311]: (u1_struct_0(g1_pre_topc(A_310, B_311))=A_310 | ~m1_subset_1(B_311, k1_zfmisc_1(k1_zfmisc_1(A_310))) | ~v1_pre_topc(g1_pre_topc(A_310, B_311)) | ~l1_pre_topc(g1_pre_topc(A_310, B_311)))), inference(reflexivity, [status(thm), theory('equality')], [c_126])).
% 12.35/4.70  tff(c_6308, plain, (![A_313]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_313), u1_pre_topc(A_313)))=u1_struct_0(A_313) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_313), u1_pre_topc(A_313))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_313), u1_pre_topc(A_313))) | ~l1_pre_topc(A_313))), inference(resolution, [status(thm)], [c_18, c_6295])).
% 12.35/4.70  tff(c_6316, plain, (![A_314]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_314), u1_pre_topc(A_314)))=u1_struct_0(A_314) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_314), u1_pre_topc(A_314))) | ~l1_pre_topc(A_314))), inference(resolution, [status(thm)], [c_69, c_6308])).
% 12.35/4.70  tff(c_6324, plain, (![A_315]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_315), u1_pre_topc(A_315)))=u1_struct_0(A_315) | ~l1_pre_topc(A_315))), inference(resolution, [status(thm)], [c_75, c_6316])).
% 12.35/4.70  tff(c_104, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_12])).
% 12.35/4.70  tff(c_110, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_104])).
% 12.35/4.70  tff(c_182, plain, (![A_68, B_69]: (v1_compts_1(k1_pre_topc(A_68, B_69)) | ~v2_compts_1(B_69, A_68) | k1_xboole_0=B_69 | ~v2_pre_topc(A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.70  tff(c_185, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_182])).
% 12.35/4.70  tff(c_188, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_77, c_185])).
% 12.35/4.70  tff(c_189, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_188])).
% 12.35/4.70  tff(c_204, plain, (![A_71]: (v1_compts_1(k1_pre_topc(A_71, '#skF_3')) | ~v2_compts_1('#skF_3', A_71) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_189, c_189, c_38])).
% 12.35/4.70  tff(c_207, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_204])).
% 12.35/4.70  tff(c_210, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_77, c_207])).
% 12.35/4.70  tff(c_116, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_110, c_16])).
% 12.35/4.70  tff(c_119, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_116])).
% 12.35/4.70  tff(c_251, plain, (![A_84, B_85]: (u1_struct_0(g1_pre_topc(A_84, B_85))=A_84 | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))) | ~v1_pre_topc(g1_pre_topc(A_84, B_85)) | ~l1_pre_topc(g1_pre_topc(A_84, B_85)))), inference(reflexivity, [status(thm), theory('equality')], [c_126])).
% 12.35/4.70  tff(c_286, plain, (![A_91]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91)))=u1_struct_0(A_91) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_18, c_251])).
% 12.35/4.70  tff(c_294, plain, (![A_92]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_92), u1_pre_topc(A_92)))=u1_struct_0(A_92) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_92), u1_pre_topc(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_69, c_286])).
% 12.35/4.70  tff(c_302, plain, (![A_93]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_93), u1_pre_topc(A_93)))=u1_struct_0(A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_75, c_294])).
% 12.35/4.70  tff(c_107, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_14])).
% 12.35/4.70  tff(c_113, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_107])).
% 12.35/4.70  tff(c_256, plain, (![A_86, B_87]: (k2_struct_0(k1_pre_topc(A_86, B_87))=B_87 | ~m1_pre_topc(k1_pre_topc(A_86, B_87), A_86) | ~v1_pre_topc(k1_pre_topc(A_86, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.35/4.70  tff(c_261, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_110, c_256])).
% 12.35/4.70  tff(c_265, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101, c_113, c_261])).
% 12.35/4.70  tff(c_269, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_265, c_4])).
% 12.35/4.70  tff(c_273, plain, (![A_2]: (k1_pre_topc(A_2, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_265, c_269])).
% 12.35/4.70  tff(c_369, plain, (![A_94]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94))) | ~l1_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_302, c_273])).
% 12.35/4.70  tff(c_376, plain, (![B_26]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_26))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_369])).
% 12.35/4.71  tff(c_2133, plain, (![B_152]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_152), u1_pre_topc(B_152)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_152))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_152), u1_pre_topc(B_152))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_152) | ~l1_pre_topc(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_376])).
% 12.35/4.71  tff(c_2159, plain, (![A_153]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_153) | ~l1_pre_topc(A_153))), inference(resolution, [status(thm)], [c_75, c_2133])).
% 12.35/4.71  tff(c_191, plain, (![A_27]: (v2_compts_1('#skF_3', A_27) | ~v1_compts_1(k1_pre_topc(A_27, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_189, c_189, c_36])).
% 12.35/4.71  tff(c_327, plain, (![A_93]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_93), u1_pre_topc(A_93))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_93), u1_pre_topc(A_93)), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_93), u1_pre_topc(A_93))) | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_302, c_191])).
% 12.35/4.71  tff(c_2165, plain, (![A_153]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153))) | ~l1_pre_topc(A_153) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_153) | ~l1_pre_topc(A_153))), inference(superposition, [status(thm), theory('equality')], [c_2159, c_327])).
% 12.35/4.71  tff(c_2220, plain, (![A_154]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_154), u1_pre_topc(A_154))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_154), u1_pre_topc(A_154))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_154) | ~l1_pre_topc(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_2165])).
% 12.35/4.71  tff(c_140, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_50])).
% 12.35/4.71  tff(c_2223, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2220, c_140])).
% 12.35/4.71  tff(c_2247, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_110, c_101, c_2223])).
% 12.35/4.71  tff(c_2284, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_2247])).
% 12.35/4.71  tff(c_2290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2284])).
% 12.35/4.71  tff(c_2292, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 12.35/4.71  tff(c_2291, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_188])).
% 12.35/4.71  tff(c_2322, plain, (![A_167, B_168]: (u1_struct_0(g1_pre_topc(A_167, B_168))=A_167 | ~m1_subset_1(B_168, k1_zfmisc_1(k1_zfmisc_1(A_167))) | ~v1_pre_topc(g1_pre_topc(A_167, B_168)) | ~l1_pre_topc(g1_pre_topc(A_167, B_168)))), inference(reflexivity, [status(thm), theory('equality')], [c_126])).
% 12.35/4.71  tff(c_2362, plain, (![A_173]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_173), u1_pre_topc(A_173)))=u1_struct_0(A_173) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_173), u1_pre_topc(A_173))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_173), u1_pre_topc(A_173))) | ~l1_pre_topc(A_173))), inference(resolution, [status(thm)], [c_18, c_2322])).
% 12.35/4.71  tff(c_2421, plain, (![A_176]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_176), u1_pre_topc(A_176)))=u1_struct_0(A_176) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_176), u1_pre_topc(A_176))) | ~l1_pre_topc(A_176))), inference(resolution, [status(thm)], [c_69, c_2362])).
% 12.35/4.71  tff(c_2432, plain, (![A_177]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177)))=u1_struct_0(A_177) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_75, c_2421])).
% 12.35/4.71  tff(c_2327, plain, (![A_169, B_170]: (k2_struct_0(k1_pre_topc(A_169, B_170))=B_170 | ~m1_pre_topc(k1_pre_topc(A_169, B_170), A_169) | ~v1_pre_topc(k1_pre_topc(A_169, B_170)) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.35/4.71  tff(c_2332, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_110, c_2327])).
% 12.35/4.71  tff(c_2336, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101, c_113, c_2332])).
% 12.35/4.71  tff(c_2340, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_2336, c_4])).
% 12.35/4.71  tff(c_2344, plain, (![A_2]: (k1_pre_topc(A_2, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2336, c_2340])).
% 12.35/4.71  tff(c_2542, plain, (![A_182]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_182), u1_pre_topc(A_182)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0(A_182), u1_pre_topc(A_182))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_182), u1_pre_topc(A_182))) | ~l1_pre_topc(A_182))), inference(superposition, [status(thm), theory('equality')], [c_2432, c_2344])).
% 12.35/4.71  tff(c_2552, plain, (![B_26]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_26))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_26) | ~l1_pre_topc(B_26) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_2542])).
% 12.35/4.71  tff(c_4237, plain, (![B_238]: (k1_pre_topc(g1_pre_topc(u1_struct_0(B_238), u1_pre_topc(B_238)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(B_238))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_238), u1_pre_topc(B_238))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_238) | ~l1_pre_topc(B_238))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2552])).
% 12.35/4.71  tff(c_4262, plain, (![A_16]: (k1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16)), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_75, c_4237])).
% 12.35/4.71  tff(c_5963, plain, (![B_270, A_271]: (v2_compts_1(B_270, g1_pre_topc(u1_struct_0(A_271), u1_pre_topc(A_271))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_271), u1_pre_topc(A_271)), B_270)) | k1_xboole_0=B_270 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_271), u1_pre_topc(A_271))) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_271), u1_pre_topc(A_271))) | ~l1_pre_topc(A_271))), inference(superposition, [status(thm), theory('equality')], [c_2432, c_32])).
% 12.35/4.71  tff(c_5975, plain, (![A_16]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_16) | ~l1_pre_topc(A_16))), inference(superposition, [status(thm), theory('equality')], [c_4262, c_5963])).
% 12.35/4.71  tff(c_6001, plain, (![A_16]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_16) | ~l1_pre_topc(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2291, c_5975])).
% 12.35/4.71  tff(c_6005, plain, (![A_272]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_272), u1_pre_topc(A_272))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_272), u1_pre_topc(A_272))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_272), u1_pre_topc(A_272))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_272))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_272) | ~l1_pre_topc(A_272))), inference(negUnitSimplification, [status(thm)], [c_2292, c_6001])).
% 12.35/4.71  tff(c_6008, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6005, c_140])).
% 12.35/4.71  tff(c_6038, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_110, c_101, c_6008])).
% 12.35/4.71  tff(c_6118, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_6038])).
% 12.35/4.71  tff(c_6124, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_6118])).
% 12.35/4.71  tff(c_6130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_6124])).
% 12.35/4.71  tff(c_6131, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_6038])).
% 12.35/4.71  tff(c_6140, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_6131])).
% 12.35/4.71  tff(c_6147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6140])).
% 12.35/4.71  tff(c_6148, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 12.35/4.71  tff(c_6172, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_6148])).
% 12.35/4.71  tff(c_6355, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6324, c_6172])).
% 12.35/4.71  tff(c_6394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_101, c_6355])).
% 12.35/4.71  tff(c_6396, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_6148])).
% 12.35/4.71  tff(c_6412, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_6396, c_14])).
% 12.35/4.71  tff(c_6416, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_6412])).
% 12.35/4.71  tff(c_6422, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_6416])).
% 12.35/4.71  tff(c_6428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_6422])).
% 12.35/4.71  tff(c_6430, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_6412])).
% 12.35/4.71  tff(c_6149, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 12.35/4.71  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.71  tff(c_7380, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_6149, c_6396, c_48])).
% 12.35/4.71  tff(c_7388, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7380, c_12])).
% 12.35/4.71  tff(c_7403, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_7388])).
% 12.35/4.71  tff(c_7421, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7403, c_16])).
% 12.35/4.71  tff(c_7436, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_7421])).
% 12.35/4.71  tff(c_28, plain, (![A_24, B_26]: (m1_pre_topc(A_24, B_26) | ~m1_pre_topc(A_24, g1_pre_topc(u1_struct_0(B_26), u1_pre_topc(B_26))) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.35/4.71  tff(c_7418, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(resolution, [status(thm)], [c_7403, c_28])).
% 12.35/4.71  tff(c_7433, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7418])).
% 12.35/4.71  tff(c_7493, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7436, c_7433])).
% 12.35/4.71  tff(c_7391, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7380, c_14])).
% 12.35/4.71  tff(c_7406, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_7391])).
% 12.35/4.71  tff(c_6, plain, (![A_2, B_6]: (k2_struct_0(k1_pre_topc(A_2, B_6))=B_6 | ~m1_pre_topc(k1_pre_topc(A_2, B_6), A_2) | ~v1_pre_topc(k1_pre_topc(A_2, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.35/4.71  tff(c_7415, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7403, c_6])).
% 12.35/4.71  tff(c_7430, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_7380, c_7406, c_7415])).
% 12.35/4.71  tff(c_7467, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_2) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_7430, c_4])).
% 12.35/4.71  tff(c_7842, plain, (![A_375]: (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc(A_375, '#skF_2') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_375) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375))), inference(demodulation, [status(thm), theory('equality')], [c_7406, c_7430, c_7467])).
% 12.35/4.71  tff(c_7845, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7493, c_7842])).
% 12.35/4.71  tff(c_7858, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7845])).
% 12.35/4.71  tff(c_8033, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7858])).
% 12.35/4.71  tff(c_128, plain, (![A_1, C_46, D_48]: (u1_struct_0(A_1)=C_46 | g1_pre_topc(C_46, D_48)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 12.35/4.71  tff(c_7808, plain, (![C_373, D_374]: (u1_struct_0(g1_pre_topc(C_373, D_374))=C_373 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_373, D_374)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_373, D_374))))) | ~v1_pre_topc(g1_pre_topc(C_373, D_374)) | ~l1_pre_topc(g1_pre_topc(C_373, D_374)))), inference(reflexivity, [status(thm), theory('equality')], [c_128])).
% 12.35/4.71  tff(c_7954, plain, (![C_376, D_377]: (u1_struct_0(g1_pre_topc(C_376, D_377))=C_376 | ~v1_pre_topc(g1_pre_topc(C_376, D_377)) | ~l1_pre_topc(g1_pre_topc(C_376, D_377)))), inference(resolution, [status(thm)], [c_18, c_7808])).
% 12.35/4.71  tff(c_8049, plain, (![A_382]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_382), u1_pre_topc(A_382)))=u1_struct_0(A_382) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_382), u1_pre_topc(A_382))) | ~l1_pre_topc(A_382))), inference(resolution, [status(thm)], [c_69, c_7954])).
% 12.35/4.71  tff(c_8061, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6430, c_8049])).
% 12.35/4.71  tff(c_8074, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8061])).
% 12.35/4.71  tff(c_8085, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8074, c_7380])).
% 12.35/4.71  tff(c_8093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8033, c_8085])).
% 12.35/4.71  tff(c_8095, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7858])).
% 12.35/4.71  tff(c_8101, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8095, c_32])).
% 12.35/4.71  tff(c_8112, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_8101])).
% 12.35/4.71  tff(c_8113, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_102, c_8112])).
% 12.35/4.71  tff(c_8164, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_8113])).
% 12.35/4.71  tff(c_8094, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_7858])).
% 12.35/4.71  tff(c_6395, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_6148])).
% 12.35/4.71  tff(c_34, plain, (![A_27, B_29]: (v1_compts_1(k1_pre_topc(A_27, B_29)) | ~v2_compts_1(B_29, A_27) | k1_xboole_0=B_29 | ~v2_pre_topc(A_27) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.71  tff(c_7383, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7380, c_34])).
% 12.35/4.71  tff(c_7397, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6395, c_7383])).
% 12.35/4.71  tff(c_7446, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_7397])).
% 12.35/4.71  tff(c_7449, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_7446])).
% 12.35/4.71  tff(c_7456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_7449])).
% 12.35/4.71  tff(c_7457, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_7397])).
% 12.35/4.71  tff(c_7478, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_7457])).
% 12.35/4.71  tff(c_8176, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8094, c_7478])).
% 12.35/4.71  tff(c_8183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8164, c_8176])).
% 12.35/4.71  tff(c_8185, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_8113])).
% 12.35/4.71  tff(c_8184, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8113])).
% 12.35/4.71  tff(c_8264, plain, (![A_386]: (v2_compts_1('#skF_2', A_386) | ~v1_compts_1(k1_pre_topc(A_386, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_386))) | ~l1_pre_topc(A_386))), inference(demodulation, [status(thm), theory('equality')], [c_8184, c_8184, c_8184, c_36])).
% 12.35/4.71  tff(c_8267, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8095, c_8264])).
% 12.35/4.71  tff(c_8273, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8185, c_8267])).
% 12.35/4.71  tff(c_8275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_8273])).
% 12.35/4.71  tff(c_8277, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_7457])).
% 12.35/4.71  tff(c_8276, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7457])).
% 12.35/4.71  tff(c_8292, plain, (![A_387]: (v1_compts_1(k1_pre_topc(A_387, '#skF_2')) | ~v2_compts_1('#skF_2', A_387) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_387))) | ~l1_pre_topc(A_387))), inference(demodulation, [status(thm), theory('equality')], [c_8276, c_8276, c_8276, c_38])).
% 12.35/4.71  tff(c_8295, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7380, c_8292])).
% 12.35/4.71  tff(c_8298, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6395, c_8295])).
% 12.35/4.71  tff(c_8300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8277, c_8298])).
% 12.35/4.71  tff(c_8302, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 12.35/4.71  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.71  tff(c_14390, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_14383, c_8302, c_46])).
% 12.35/4.71  tff(c_14391, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_14390])).
% 12.35/4.71  tff(c_14558, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14531, c_14391])).
% 12.35/4.71  tff(c_14597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_101, c_14558])).
% 12.35/4.71  tff(c_14598, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_14390])).
% 12.35/4.71  tff(c_14599, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_14390])).
% 12.35/4.71  tff(c_14609, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_14599, c_14])).
% 12.35/4.71  tff(c_14612, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_14609])).
% 12.35/4.71  tff(c_14618, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_14612])).
% 12.35/4.71  tff(c_14624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_14618])).
% 12.35/4.71  tff(c_14626, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_14609])).
% 12.35/4.71  tff(c_14992, plain, (![A_681, B_682]: (u1_struct_0(g1_pre_topc(A_681, B_682))=A_681 | ~m1_subset_1(B_682, k1_zfmisc_1(k1_zfmisc_1(A_681))) | ~v1_pre_topc(g1_pre_topc(A_681, B_682)) | ~l1_pre_topc(g1_pre_topc(A_681, B_682)))), inference(reflexivity, [status(thm), theory('equality')], [c_8337])).
% 12.35/4.71  tff(c_15066, plain, (![A_684]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_684), u1_pre_topc(A_684)))=u1_struct_0(A_684) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_684), u1_pre_topc(A_684))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_684), u1_pre_topc(A_684))) | ~l1_pre_topc(A_684))), inference(resolution, [status(thm)], [c_18, c_14992])).
% 12.35/4.71  tff(c_15074, plain, (![A_685]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_685), u1_pre_topc(A_685)))=u1_struct_0(A_685) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_685), u1_pre_topc(A_685))) | ~l1_pre_topc(A_685))), inference(resolution, [status(thm)], [c_69, c_15066])).
% 12.35/4.71  tff(c_15077, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14626, c_15074])).
% 12.35/4.71  tff(c_15086, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_15077])).
% 12.35/4.71  tff(c_14628, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_14383, c_14599, c_48])).
% 12.35/4.71  tff(c_15101, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15086, c_14628])).
% 12.35/4.71  tff(c_15104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14598, c_15101])).
% 12.35/4.71  tff(c_15106, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 12.35/4.71  tff(c_15112, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_15106, c_52])).
% 12.35/4.71  tff(c_15113, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_15112])).
% 12.35/4.71  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.71  tff(c_15151, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_15106, c_54])).
% 12.35/4.71  tff(c_15161, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15151, c_14])).
% 12.35/4.71  tff(c_15165, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15161])).
% 12.35/4.71  tff(c_15171, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_15165])).
% 12.35/4.71  tff(c_15177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_15171])).
% 12.35/4.71  tff(c_15179, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_15161])).
% 12.35/4.71  tff(c_15119, plain, (![C_688, A_689, D_690, B_691]: (C_688=A_689 | g1_pre_topc(C_688, D_690)!=g1_pre_topc(A_689, B_691) | ~m1_subset_1(B_691, k1_zfmisc_1(k1_zfmisc_1(A_689))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.71  tff(c_15121, plain, (![A_1, A_689, B_691]: (u1_struct_0(A_1)=A_689 | g1_pre_topc(A_689, B_691)!=A_1 | ~m1_subset_1(B_691, k1_zfmisc_1(k1_zfmisc_1(A_689))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15119])).
% 12.35/4.71  tff(c_15270, plain, (![A_722, B_723]: (u1_struct_0(g1_pre_topc(A_722, B_723))=A_722 | ~m1_subset_1(B_723, k1_zfmisc_1(k1_zfmisc_1(A_722))) | ~v1_pre_topc(g1_pre_topc(A_722, B_723)) | ~l1_pre_topc(g1_pre_topc(A_722, B_723)))), inference(reflexivity, [status(thm), theory('equality')], [c_15121])).
% 12.35/4.71  tff(c_15350, plain, (![A_728]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_728), u1_pre_topc(A_728)))=u1_struct_0(A_728) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_728), u1_pre_topc(A_728))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_728), u1_pre_topc(A_728))) | ~l1_pre_topc(A_728))), inference(resolution, [status(thm)], [c_18, c_15270])).
% 12.35/4.71  tff(c_15358, plain, (![A_729]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_729), u1_pre_topc(A_729)))=u1_struct_0(A_729) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_729), u1_pre_topc(A_729))) | ~l1_pre_topc(A_729))), inference(resolution, [status(thm)], [c_69, c_15350])).
% 12.35/4.71  tff(c_15361, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15179, c_15358])).
% 12.35/4.71  tff(c_15370, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_15361])).
% 12.35/4.71  tff(c_15372, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15370, c_15151])).
% 12.35/4.71  tff(c_15469, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15372, c_32])).
% 12.35/4.71  tff(c_15480, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_15469])).
% 12.35/4.71  tff(c_15481, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_15113, c_15480])).
% 12.35/4.71  tff(c_15508, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_15481])).
% 12.35/4.71  tff(c_15160, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15151, c_12])).
% 12.35/4.71  tff(c_15282, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15179, c_15160])).
% 12.35/4.71  tff(c_15290, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15282, c_16])).
% 12.35/4.71  tff(c_15305, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15179, c_15290])).
% 12.35/4.71  tff(c_15287, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(resolution, [status(thm)], [c_15282, c_28])).
% 12.35/4.71  tff(c_15302, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_15287])).
% 12.35/4.71  tff(c_15330, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15305, c_15302])).
% 12.35/4.71  tff(c_15178, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_15161])).
% 12.35/4.71  tff(c_15284, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15282, c_6])).
% 12.35/4.71  tff(c_15299, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15179, c_15151, c_15178, c_15284])).
% 12.35/4.71  tff(c_15318, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_2) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_15299, c_4])).
% 12.35/4.71  tff(c_16197, plain, (![A_748]: (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc(A_748, '#skF_2') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_748) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_748))) | ~l1_pre_topc(A_748))), inference(demodulation, [status(thm), theory('equality')], [c_15178, c_15299, c_15318])).
% 12.35/4.71  tff(c_16204, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15330, c_16197])).
% 12.35/4.71  tff(c_16221, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_15372, c_16204])).
% 12.35/4.71  tff(c_15105, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 12.35/4.71  tff(c_15216, plain, (![A_712, B_713]: (v1_compts_1(k1_pre_topc(A_712, B_713)) | ~v2_compts_1(B_713, A_712) | k1_xboole_0=B_713 | ~v2_pre_topc(A_712) | ~m1_subset_1(B_713, k1_zfmisc_1(u1_struct_0(A_712))) | ~l1_pre_topc(A_712))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.71  tff(c_15219, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15151, c_15216])).
% 12.35/4.71  tff(c_15222, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15179, c_15105, c_15219])).
% 12.35/4.71  tff(c_15223, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15222])).
% 12.35/4.71  tff(c_15226, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_15223])).
% 12.35/4.71  tff(c_15233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_15226])).
% 12.35/4.71  tff(c_15234, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_15222])).
% 12.35/4.71  tff(c_15241, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_15234])).
% 12.35/4.71  tff(c_16236, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16221, c_15241])).
% 12.35/4.71  tff(c_16242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15508, c_16236])).
% 12.35/4.71  tff(c_16244, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_15481])).
% 12.35/4.71  tff(c_16243, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_15481])).
% 12.35/4.71  tff(c_16530, plain, (![A_758]: (v2_compts_1('#skF_2', A_758) | ~v1_compts_1(k1_pre_topc(A_758, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_758))) | ~l1_pre_topc(A_758))), inference(demodulation, [status(thm), theory('equality')], [c_16243, c_16243, c_16243, c_36])).
% 12.35/4.71  tff(c_16539, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15372, c_16530])).
% 12.35/4.71  tff(c_16547, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16244, c_16539])).
% 12.35/4.71  tff(c_16549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15113, c_16547])).
% 12.35/4.71  tff(c_16551, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_15234])).
% 12.35/4.71  tff(c_16550, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_15234])).
% 12.35/4.71  tff(c_16570, plain, (![A_761]: (v1_compts_1(k1_pre_topc(A_761, '#skF_2')) | ~v2_compts_1('#skF_2', A_761) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_761))) | ~l1_pre_topc(A_761))), inference(demodulation, [status(thm), theory('equality')], [c_16550, c_16550, c_16550, c_38])).
% 12.35/4.71  tff(c_16573, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15151, c_16570])).
% 12.35/4.71  tff(c_16576, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15179, c_15105, c_16573])).
% 12.35/4.71  tff(c_16578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16551, c_16576])).
% 12.35/4.71  tff(c_16579, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_15112])).
% 12.35/4.71  tff(c_16581, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_15106, c_54])).
% 12.35/4.71  tff(c_16591, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_16581, c_14])).
% 12.35/4.71  tff(c_16632, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_16591])).
% 12.35/4.71  tff(c_16639, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_16632])).
% 12.35/4.71  tff(c_16645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_16639])).
% 12.35/4.71  tff(c_16647, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_16591])).
% 12.35/4.71  tff(c_16600, plain, (![D_762, B_763, C_764, A_765]: (D_762=B_763 | g1_pre_topc(C_764, D_762)!=g1_pre_topc(A_765, B_763) | ~m1_subset_1(B_763, k1_zfmisc_1(k1_zfmisc_1(A_765))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.71  tff(c_16602, plain, (![A_1, B_763, A_765]: (u1_pre_topc(A_1)=B_763 | g1_pre_topc(A_765, B_763)!=A_1 | ~m1_subset_1(B_763, k1_zfmisc_1(k1_zfmisc_1(A_765))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16600])).
% 12.35/4.71  tff(c_16739, plain, (![A_796, B_797]: (u1_pre_topc(g1_pre_topc(A_796, B_797))=B_797 | ~m1_subset_1(B_797, k1_zfmisc_1(k1_zfmisc_1(A_796))) | ~v1_pre_topc(g1_pre_topc(A_796, B_797)) | ~l1_pre_topc(g1_pre_topc(A_796, B_797)))), inference(reflexivity, [status(thm), theory('equality')], [c_16602])).
% 12.35/4.71  tff(c_16811, plain, (![A_800]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_800), u1_pre_topc(A_800)))=u1_pre_topc(A_800) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_800), u1_pre_topc(A_800))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_800), u1_pre_topc(A_800))) | ~l1_pre_topc(A_800))), inference(resolution, [status(thm)], [c_18, c_16739])).
% 12.35/4.71  tff(c_16821, plain, (![A_801]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_801), u1_pre_topc(A_801)))=u1_pre_topc(A_801) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_801), u1_pre_topc(A_801))) | ~l1_pre_topc(A_801))), inference(resolution, [status(thm)], [c_69, c_16811])).
% 12.35/4.71  tff(c_16824, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16647, c_16821])).
% 12.35/4.71  tff(c_16833, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16824])).
% 12.35/4.71  tff(c_16850, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16833, c_2])).
% 12.35/4.71  tff(c_16874, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16647, c_16850])).
% 12.35/4.71  tff(c_17333, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_16874])).
% 12.35/4.71  tff(c_17339, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_17333])).
% 12.35/4.71  tff(c_17345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_17339])).
% 12.35/4.71  tff(c_17347, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_16874])).
% 12.35/4.71  tff(c_16859, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16833, c_18])).
% 12.35/4.71  tff(c_16880, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_16647, c_16859])).
% 12.35/4.71  tff(c_16609, plain, (![C_766, A_767, D_768, B_769]: (C_766=A_767 | g1_pre_topc(C_766, D_768)!=g1_pre_topc(A_767, B_769) | ~m1_subset_1(B_769, k1_zfmisc_1(k1_zfmisc_1(A_767))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.71  tff(c_16613, plain, (![A_1, C_766, D_768]: (u1_struct_0(A_1)=C_766 | g1_pre_topc(C_766, D_768)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16609])).
% 12.35/4.71  tff(c_17442, plain, (![C_814, D_815]: (u1_struct_0(g1_pre_topc(C_814, D_815))=C_814 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_814, D_815)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_814, D_815))))) | ~v1_pre_topc(g1_pre_topc(C_814, D_815)) | ~l1_pre_topc(g1_pre_topc(C_814, D_815)))), inference(reflexivity, [status(thm), theory('equality')], [c_16613])).
% 12.35/4.71  tff(c_17454, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16833, c_17442])).
% 12.35/4.71  tff(c_17469, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16647, c_17347, c_16880, c_17454])).
% 12.35/4.71  tff(c_17473, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17469, c_16581])).
% 12.35/4.71  tff(c_17475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16579, c_17473])).
% 12.35/4.71  tff(c_17477, plain, (~v2_compts_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 12.35/4.71  tff(c_58, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.71  tff(c_17478, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_17477, c_58])).
% 12.35/4.71  tff(c_17479, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_17478])).
% 12.35/4.71  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.35/4.71  tff(c_17508, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_17477, c_60])).
% 12.35/4.71  tff(c_17518, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_17508, c_14])).
% 12.35/4.71  tff(c_17558, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_17518])).
% 12.35/4.71  tff(c_17564, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_17558])).
% 12.35/4.71  tff(c_17570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_17564])).
% 12.35/4.71  tff(c_17572, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_17518])).
% 12.35/4.71  tff(c_17534, plain, (![D_826, B_827, C_828, A_829]: (D_826=B_827 | g1_pre_topc(C_828, D_826)!=g1_pre_topc(A_829, B_827) | ~m1_subset_1(B_827, k1_zfmisc_1(k1_zfmisc_1(A_829))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.71  tff(c_17536, plain, (![A_1, B_827, A_829]: (u1_pre_topc(A_1)=B_827 | g1_pre_topc(A_829, B_827)!=A_1 | ~m1_subset_1(B_827, k1_zfmisc_1(k1_zfmisc_1(A_829))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17534])).
% 12.35/4.71  tff(c_17669, plain, (![A_858, B_859]: (u1_pre_topc(g1_pre_topc(A_858, B_859))=B_859 | ~m1_subset_1(B_859, k1_zfmisc_1(k1_zfmisc_1(A_858))) | ~v1_pre_topc(g1_pre_topc(A_858, B_859)) | ~l1_pre_topc(g1_pre_topc(A_858, B_859)))), inference(reflexivity, [status(thm), theory('equality')], [c_17536])).
% 12.35/4.71  tff(c_17736, plain, (![A_860]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_860), u1_pre_topc(A_860)))=u1_pre_topc(A_860) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_860), u1_pre_topc(A_860))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_860), u1_pre_topc(A_860))) | ~l1_pre_topc(A_860))), inference(resolution, [status(thm)], [c_18, c_17669])).
% 12.35/4.71  tff(c_17744, plain, (![A_861]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_861), u1_pre_topc(A_861)))=u1_pre_topc(A_861) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_861), u1_pre_topc(A_861))) | ~l1_pre_topc(A_861))), inference(resolution, [status(thm)], [c_69, c_17736])).
% 12.35/4.71  tff(c_17747, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17572, c_17744])).
% 12.35/4.71  tff(c_17756, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_17747])).
% 12.35/4.71  tff(c_17792, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_17756, c_18])).
% 12.35/4.71  tff(c_17815, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17792])).
% 12.35/4.71  tff(c_17525, plain, (![C_822, A_823, D_824, B_825]: (C_822=A_823 | g1_pre_topc(C_822, D_824)!=g1_pre_topc(A_823, B_825) | ~m1_subset_1(B_825, k1_zfmisc_1(k1_zfmisc_1(A_823))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.71  tff(c_17529, plain, (![A_1, C_822, D_824]: (u1_struct_0(A_1)=C_822 | g1_pre_topc(C_822, D_824)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17525])).
% 12.35/4.71  tff(c_17979, plain, (![C_865, D_866]: (u1_struct_0(g1_pre_topc(C_865, D_866))=C_865 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_865, D_866)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_865, D_866))))) | ~v1_pre_topc(g1_pre_topc(C_865, D_866)) | ~l1_pre_topc(g1_pre_topc(C_865, D_866)))), inference(reflexivity, [status(thm), theory('equality')], [c_17529])).
% 12.35/4.71  tff(c_17988, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_17756, c_17979])).
% 12.35/4.71  tff(c_18001, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17815, c_17988])).
% 12.35/4.71  tff(c_18021, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_18001])).
% 12.35/4.71  tff(c_18027, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_18021])).
% 12.35/4.71  tff(c_18033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_18027])).
% 12.35/4.71  tff(c_18034, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_18001])).
% 12.35/4.71  tff(c_18072, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18034, c_17508])).
% 12.35/4.71  tff(c_18198, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18072, c_32])).
% 12.35/4.71  tff(c_18209, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_18198])).
% 12.35/4.71  tff(c_18210, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17479, c_18209])).
% 12.35/4.71  tff(c_18228, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_18210])).
% 12.35/4.71  tff(c_17517, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_17508, c_12])).
% 12.35/4.71  tff(c_17675, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17517])).
% 12.35/4.71  tff(c_17683, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_17675, c_16])).
% 12.35/4.71  tff(c_17698, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17683])).
% 12.35/4.71  tff(c_17680, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(resolution, [status(thm)], [c_17675, c_28])).
% 12.35/4.71  tff(c_17695, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_17680])).
% 12.35/4.71  tff(c_17724, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17698, c_17695])).
% 12.35/4.71  tff(c_17571, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_17518])).
% 12.35/4.71  tff(c_17677, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_17675, c_6])).
% 12.35/4.71  tff(c_17692, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17508, c_17571, c_17677])).
% 12.35/4.71  tff(c_17712, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_2) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_17692, c_4])).
% 12.35/4.71  tff(c_18523, plain, (![A_880]: (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc(A_880, '#skF_2') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_880) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_880))) | ~l1_pre_topc(A_880))), inference(demodulation, [status(thm), theory('equality')], [c_17571, c_17692, c_17712])).
% 12.35/4.71  tff(c_18526, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17724, c_18523])).
% 12.35/4.71  tff(c_18539, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18072, c_18526])).
% 12.35/4.71  tff(c_17476, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 12.35/4.71  tff(c_17610, plain, (![A_846, B_847]: (v1_compts_1(k1_pre_topc(A_846, B_847)) | ~v2_compts_1(B_847, A_846) | k1_xboole_0=B_847 | ~v2_pre_topc(A_846) | ~m1_subset_1(B_847, k1_zfmisc_1(u1_struct_0(A_846))) | ~l1_pre_topc(A_846))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.35/4.71  tff(c_17613, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_17508, c_17610])).
% 12.35/4.71  tff(c_17616, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17476, c_17613])).
% 12.35/4.71  tff(c_17617, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_17616])).
% 12.35/4.71  tff(c_17620, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_17617])).
% 12.35/4.71  tff(c_17627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_17620])).
% 12.35/4.71  tff(c_17628, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_17616])).
% 12.35/4.71  tff(c_17635, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_17628])).
% 12.35/4.71  tff(c_18554, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18539, c_17635])).
% 12.35/4.71  tff(c_18560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18228, c_18554])).
% 12.35/4.71  tff(c_18562, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_18210])).
% 12.35/4.71  tff(c_18561, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18210])).
% 12.35/4.71  tff(c_18662, plain, (![A_887]: (v2_compts_1('#skF_2', A_887) | ~v1_compts_1(k1_pre_topc(A_887, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_887))) | ~l1_pre_topc(A_887))), inference(demodulation, [status(thm), theory('equality')], [c_18561, c_18561, c_18561, c_36])).
% 12.35/4.71  tff(c_18665, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18072, c_18662])).
% 12.35/4.71  tff(c_18671, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18562, c_18665])).
% 12.35/4.71  tff(c_18673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17479, c_18671])).
% 12.35/4.71  tff(c_18675, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_17628])).
% 12.35/4.71  tff(c_18674, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17628])).
% 12.35/4.71  tff(c_18701, plain, (![A_891]: (v1_compts_1(k1_pre_topc(A_891, '#skF_2')) | ~v2_compts_1('#skF_2', A_891) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_891))) | ~l1_pre_topc(A_891))), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_18674, c_18674, c_38])).
% 12.35/4.71  tff(c_18704, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_17508, c_18701])).
% 12.35/4.71  tff(c_18707, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_17572, c_17476, c_18704])).
% 12.35/4.71  tff(c_18709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18675, c_18707])).
% 12.35/4.71  tff(c_18710, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_17478])).
% 12.35/4.71  tff(c_18712, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_17477, c_60])).
% 12.35/4.71  tff(c_18743, plain, (![A_894, B_895]: (v1_pre_topc(k1_pre_topc(A_894, B_895)) | ~m1_subset_1(B_895, k1_zfmisc_1(u1_struct_0(A_894))) | ~l1_pre_topc(A_894))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.35/4.71  tff(c_18747, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_18712, c_18743])).
% 12.35/4.71  tff(c_18792, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_18747])).
% 12.35/4.71  tff(c_18798, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_75, c_18792])).
% 12.35/4.71  tff(c_18804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_18798])).
% 12.35/4.71  tff(c_18806, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_18747])).
% 12.35/4.71  tff(c_18769, plain, (![C_902, A_903, D_904, B_905]: (C_902=A_903 | g1_pre_topc(C_902, D_904)!=g1_pre_topc(A_903, B_905) | ~m1_subset_1(B_905, k1_zfmisc_1(k1_zfmisc_1(A_903))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.35/4.71  tff(c_18771, plain, (![A_1, A_903, B_905]: (u1_struct_0(A_1)=A_903 | g1_pre_topc(A_903, B_905)!=A_1 | ~m1_subset_1(B_905, k1_zfmisc_1(k1_zfmisc_1(A_903))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18769])).
% 12.35/4.71  tff(c_18897, plain, (![A_930, B_931]: (u1_struct_0(g1_pre_topc(A_930, B_931))=A_930 | ~m1_subset_1(B_931, k1_zfmisc_1(k1_zfmisc_1(A_930))) | ~v1_pre_topc(g1_pre_topc(A_930, B_931)) | ~l1_pre_topc(g1_pre_topc(A_930, B_931)))), inference(reflexivity, [status(thm), theory('equality')], [c_18771])).
% 12.35/4.71  tff(c_18974, plain, (![A_936]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_936), u1_pre_topc(A_936)))=u1_struct_0(A_936) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_936), u1_pre_topc(A_936))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_936), u1_pre_topc(A_936))) | ~l1_pre_topc(A_936))), inference(resolution, [status(thm)], [c_18, c_18897])).
% 12.35/4.71  tff(c_18982, plain, (![A_937]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_937), u1_pre_topc(A_937)))=u1_struct_0(A_937) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_937), u1_pre_topc(A_937))) | ~l1_pre_topc(A_937))), inference(resolution, [status(thm)], [c_69, c_18974])).
% 12.35/4.71  tff(c_18985, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18806, c_18982])).
% 12.35/4.71  tff(c_18994, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18985])).
% 12.35/4.71  tff(c_18996, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18994, c_18712])).
% 12.35/4.71  tff(c_18998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18710, c_18996])).
% 12.35/4.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.35/4.71  
% 12.35/4.71  Inference rules
% 12.35/4.71  ----------------------
% 12.35/4.71  #Ref     : 60
% 12.35/4.71  #Sup     : 5055
% 12.35/4.71  #Fact    : 0
% 12.35/4.71  #Define  : 0
% 12.35/4.71  #Split   : 48
% 12.35/4.71  #Chain   : 0
% 12.35/4.71  #Close   : 0
% 12.35/4.71  
% 12.35/4.71  Ordering : KBO
% 12.35/4.71  
% 12.35/4.71  Simplification rules
% 12.35/4.71  ----------------------
% 12.35/4.71  #Subsume      : 735
% 12.35/4.71  #Demod        : 2360
% 12.35/4.71  #Tautology    : 877
% 12.35/4.71  #SimpNegUnit  : 38
% 12.35/4.71  #BackRed      : 165
% 12.35/4.71  
% 12.35/4.71  #Partial instantiations: 0
% 12.35/4.71  #Strategies tried      : 1
% 12.35/4.71  
% 12.35/4.71  Timing (in seconds)
% 12.35/4.71  ----------------------
% 12.35/4.71  Preprocessing        : 0.31
% 12.35/4.71  Parsing              : 0.16
% 12.35/4.71  CNF conversion       : 0.02
% 12.35/4.71  Main loop            : 3.52
% 12.35/4.71  Inferencing          : 1.02
% 12.35/4.71  Reduction            : 1.07
% 12.35/4.71  Demodulation         : 0.74
% 12.35/4.71  BG Simplification    : 0.18
% 12.35/4.71  Subsumption          : 1.04
% 12.35/4.71  Abstraction          : 0.21
% 12.35/4.71  MUC search           : 0.00
% 12.35/4.71  Cooper               : 0.00
% 12.35/4.71  Total                : 3.97
% 12.35/4.71  Index Insertion      : 0.00
% 12.35/4.71  Index Deletion       : 0.00
% 12.35/4.71  Index Matching       : 0.00
% 12.35/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
