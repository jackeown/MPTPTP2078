%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:03 EST 2020

% Result     : Theorem 19.09s
% Output     : CNFRefutation 19.39s
% Verified   : 
% Statistics : Number of formulae       :  506 (5507 expanded)
%              Number of leaves         :   30 (1716 expanded)
%              Depth                    :   27
%              Number of atoms          : 1236 (17184 expanded)
%              Number of equality atoms :  280 (2126 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_compts_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v2_compts_1(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))
             => ( B = C
               => g1_pre_topc(u1_struct_0(k1_pre_topc(A,B)),u1_pre_topc(k1_pre_topc(A,B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_14,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    ! [A_34,B_35] :
      ( l1_pre_topc(g1_pre_topc(A_34,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_9] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_59,plain,(
    ! [A_31,B_32] :
      ( v1_pre_topc(g1_pre_topc(A_31,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_9] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17700,plain,(
    ! [C_586,A_587,D_588,B_589] :
      ( C_586 = A_587
      | g1_pre_topc(C_586,D_588) != g1_pre_topc(A_587,B_589)
      | ~ m1_subset_1(B_589,k1_zfmisc_1(k1_zfmisc_1(A_587))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_17702,plain,(
    ! [A_1,A_587,B_589] :
      ( u1_struct_0(A_1) = A_587
      | g1_pre_topc(A_587,B_589) != A_1
      | ~ m1_subset_1(B_589,k1_zfmisc_1(k1_zfmisc_1(A_587)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17700])).

tff(c_33432,plain,(
    ! [A_1040,B_1041] :
      ( u1_struct_0(g1_pre_topc(A_1040,B_1041)) = A_1040
      | ~ m1_subset_1(B_1041,k1_zfmisc_1(k1_zfmisc_1(A_1040)))
      | ~ v1_pre_topc(g1_pre_topc(A_1040,B_1041))
      | ~ l1_pre_topc(g1_pre_topc(A_1040,B_1041)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17702])).

tff(c_33445,plain,(
    ! [A_1046] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1046),u1_pre_topc(A_1046))) = u1_struct_0(A_1046)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1046),u1_pre_topc(A_1046)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1046),u1_pre_topc(A_1046)))
      | ~ l1_pre_topc(A_1046) ) ),
    inference(resolution,[status(thm)],[c_14,c_33432])).

tff(c_33453,plain,(
    ! [A_1047] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1047),u1_pre_topc(A_1047))) = u1_struct_0(A_1047)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1047),u1_pre_topc(A_1047)))
      | ~ l1_pre_topc(A_1047) ) ),
    inference(resolution,[status(thm)],[c_63,c_33445])).

tff(c_33461,plain,(
    ! [A_1048] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1048),u1_pre_topc(A_1048))) = u1_struct_0(A_1048)
      | ~ l1_pre_topc(A_1048) ) ),
    inference(resolution,[status(thm)],[c_69,c_33453])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16,plain,(
    ! [A_10] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_10),u1_pre_topc(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_17714,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_56,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_71,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_17747,plain,(
    ! [A_604,B_605] :
      ( v1_compts_1(k1_pre_topc(A_604,B_605))
      | ~ v2_compts_1(B_605,A_604)
      | k1_xboole_0 = B_605
      | ~ v2_pre_topc(A_604)
      | ~ m1_subset_1(B_605,k1_zfmisc_1(u1_struct_0(A_604)))
      | ~ l1_pre_topc(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17750,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_17747])).

tff(c_17753,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_71,c_17750])).

tff(c_17754,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17753])).

tff(c_32,plain,(
    ! [A_24] :
      ( v1_compts_1(k1_pre_topc(A_24,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_24)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17765,plain,(
    ! [A_606] :
      ( v1_compts_1(k1_pre_topc(A_606,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_606)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_606)))
      | ~ l1_pre_topc(A_606) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17754,c_17754,c_17754,c_32])).

tff(c_17768,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_17765])).

tff(c_17771,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71,c_17768])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_pre_topc(k1_pre_topc(A_4,B_5),A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17678,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_8])).

tff(c_17684,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17678])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( l1_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17691,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17684,c_12])).

tff(c_17694,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17691])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( v1_pre_topc(k1_pre_topc(A_4,B_5))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17681,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_10])).

tff(c_17687,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17681])).

tff(c_17821,plain,(
    ! [A_622,B_623] :
      ( u1_struct_0(g1_pre_topc(A_622,B_623)) = A_622
      | ~ m1_subset_1(B_623,k1_zfmisc_1(k1_zfmisc_1(A_622)))
      | ~ v1_pre_topc(g1_pre_topc(A_622,B_623))
      | ~ l1_pre_topc(g1_pre_topc(A_622,B_623)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17702])).

tff(c_17978,plain,(
    ! [A_632] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_632),u1_pre_topc(A_632))) = u1_struct_0(A_632)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_632),u1_pre_topc(A_632)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_632),u1_pre_topc(A_632)))
      | ~ l1_pre_topc(A_632) ) ),
    inference(resolution,[status(thm)],[c_14,c_17821])).

tff(c_17992,plain,(
    ! [A_633] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_633),u1_pre_topc(A_633))) = u1_struct_0(A_633)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_633),u1_pre_topc(A_633)))
      | ~ l1_pre_topc(A_633) ) ),
    inference(resolution,[status(thm)],[c_63,c_17978])).

tff(c_18006,plain,(
    ! [A_634] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634))) = u1_struct_0(A_634)
      | ~ l1_pre_topc(A_634) ) ),
    inference(resolution,[status(thm)],[c_69,c_17992])).

tff(c_18978,plain,(
    ! [A_668] :
      ( g1_pre_topc(u1_struct_0(A_668),u1_pre_topc(g1_pre_topc(u1_struct_0(A_668),u1_pre_topc(A_668)))) = g1_pre_topc(u1_struct_0(A_668),u1_pre_topc(A_668))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_668),u1_pre_topc(A_668)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_668),u1_pre_topc(A_668)))
      | ~ l1_pre_topc(A_668) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18006,c_2])).

tff(c_17709,plain,(
    ! [D_590,B_591,C_592,A_593] :
      ( D_590 = B_591
      | g1_pre_topc(C_592,D_590) != g1_pre_topc(A_593,B_591)
      | ~ m1_subset_1(B_591,k1_zfmisc_1(k1_zfmisc_1(A_593))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_17713,plain,(
    ! [A_1,D_590,C_592] :
      ( u1_pre_topc(A_1) = D_590
      | g1_pre_topc(C_592,D_590) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17709])).

tff(c_23765,plain,(
    ! [A_795,A_796] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_795),u1_pre_topc(A_795))) = u1_pre_topc(A_796)
      | g1_pre_topc(u1_struct_0(A_795),u1_pre_topc(A_795)) != A_796
      | ~ m1_subset_1(u1_pre_topc(A_796),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_796))))
      | ~ v1_pre_topc(A_796)
      | ~ l1_pre_topc(A_796)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_795),u1_pre_topc(A_795)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_795),u1_pre_topc(A_795)))
      | ~ l1_pre_topc(A_795) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18978,c_17713])).

tff(c_23790,plain,(
    ! [A_797,A_798] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797))) = u1_pre_topc(A_798)
      | g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797)) != A_798
      | ~ v1_pre_topc(A_798)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797)))
      | ~ l1_pre_topc(A_797)
      | ~ l1_pre_topc(A_798) ) ),
    inference(resolution,[status(thm)],[c_14,c_23765])).

tff(c_23822,plain,(
    ! [A_797] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_797),u1_pre_topc(A_797)))
      | ~ l1_pre_topc(A_797)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_17687,c_23790])).

tff(c_23844,plain,(
    ! [A_799] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_799),u1_pre_topc(A_799))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_799),u1_pre_topc(A_799)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_799),u1_pre_topc(A_799)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_799),u1_pre_topc(A_799)))
      | ~ l1_pre_topc(A_799) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17694,c_23822])).

tff(c_23885,plain,(
    ! [A_800] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_800),u1_pre_topc(A_800))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_800),u1_pre_topc(A_800)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_800),u1_pre_topc(A_800)))
      | ~ l1_pre_topc(A_800) ) ),
    inference(resolution,[status(thm)],[c_63,c_23844])).

tff(c_23926,plain,(
    ! [A_801] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_801),u1_pre_topc(A_801))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_801),u1_pre_topc(A_801)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_801) ) ),
    inference(resolution,[status(thm)],[c_69,c_23885])).

tff(c_18063,plain,(
    ! [A_634] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18006,c_69])).

tff(c_24549,plain,(
    ! [A_807] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_807),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_807),u1_pre_topc(A_807)))
      | ~ l1_pre_topc(A_807)
      | g1_pre_topc(u1_struct_0(A_807),u1_pre_topc(A_807)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_807) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23926,c_18063])).

tff(c_24579,plain,(
    ! [A_808] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_808),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | g1_pre_topc(u1_struct_0(A_808),u1_pre_topc(A_808)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_808) ) ),
    inference(resolution,[status(thm)],[c_69,c_24549])).

tff(c_24605,plain,(
    ! [A_1] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | k1_pre_topc('#skF_1','#skF_3') != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24579])).

tff(c_18066,plain,(
    ! [A_634] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18006,c_63])).

tff(c_24653,plain,(
    ! [A_810] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_810),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_810),u1_pre_topc(A_810)))
      | ~ l1_pre_topc(A_810)
      | g1_pre_topc(u1_struct_0(A_810),u1_pre_topc(A_810)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_810) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23926,c_18066])).

tff(c_24656,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24605,c_24653])).

tff(c_24687,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17694,c_17687,c_24656])).

tff(c_24818,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24687])).

tff(c_24824,plain,
    ( ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24818])).

tff(c_24830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17694,c_17687,c_24824])).

tff(c_24832,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24687])).

tff(c_24,plain,(
    ! [A_17,C_23] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_17,C_23)),u1_pre_topc(k1_pre_topc(A_17,C_23))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)),C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)))))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18037,plain,(
    ! [A_634,C_23] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_634,C_23)),u1_pre_topc(k1_pre_topc(A_634,C_23))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)),C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(A_634)
      | ~ l1_pre_topc(A_634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18006,c_24])).

tff(c_25079,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24832,c_18037])).

tff(c_25355,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_95,c_95,c_25079])).

tff(c_30,plain,(
    ! [A_24] :
      ( v2_compts_1(k1_xboole_0,A_24)
      | ~ v1_compts_1(k1_pre_topc(A_24,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17760,plain,(
    ! [A_24] :
      ( v2_compts_1('#skF_3',A_24)
      | ~ v1_compts_1(k1_pre_topc(A_24,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17754,c_17754,c_17754,c_30])).

tff(c_18046,plain,(
    ! [A_634] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_634),u1_pre_topc(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18006,c_17760])).

tff(c_25490,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25355,c_18046])).

tff(c_25561,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_17771,c_25490])).

tff(c_25562,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_17714,c_25561])).

tff(c_25611,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_25562])).

tff(c_25617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_25611])).

tff(c_25619,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17753])).

tff(c_25618,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17753])).

tff(c_17711,plain,(
    ! [A_1,B_591,A_593] :
      ( u1_pre_topc(A_1) = B_591
      | g1_pre_topc(A_593,B_591) != A_1
      | ~ m1_subset_1(B_591,k1_zfmisc_1(k1_zfmisc_1(A_593)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17709])).

tff(c_25643,plain,(
    ! [A_827,B_828] :
      ( u1_pre_topc(g1_pre_topc(A_827,B_828)) = B_828
      | ~ m1_subset_1(B_828,k1_zfmisc_1(k1_zfmisc_1(A_827)))
      | ~ v1_pre_topc(g1_pre_topc(A_827,B_828))
      | ~ l1_pre_topc(g1_pre_topc(A_827,B_828)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17711])).

tff(c_25775,plain,(
    ! [A_839] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_839),u1_pre_topc(A_839))) = u1_pre_topc(A_839)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_839),u1_pre_topc(A_839)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_839),u1_pre_topc(A_839)))
      | ~ l1_pre_topc(A_839) ) ),
    inference(resolution,[status(thm)],[c_14,c_25643])).

tff(c_25846,plain,(
    ! [A_842] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_842),u1_pre_topc(A_842))) = u1_pre_topc(A_842)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_842),u1_pre_topc(A_842)))
      | ~ l1_pre_topc(A_842) ) ),
    inference(resolution,[status(thm)],[c_63,c_25775])).

tff(c_25860,plain,(
    ! [A_843] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_843),u1_pre_topc(A_843))) = u1_pre_topc(A_843)
      | ~ l1_pre_topc(A_843) ) ),
    inference(resolution,[status(thm)],[c_69,c_25846])).

tff(c_26943,plain,(
    ! [A_879] :
      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_879),u1_pre_topc(A_879))),u1_pre_topc(A_879)) = g1_pre_topc(u1_struct_0(A_879),u1_pre_topc(A_879))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_879),u1_pre_topc(A_879)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_879),u1_pre_topc(A_879)))
      | ~ l1_pre_topc(A_879) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25860,c_2])).

tff(c_17704,plain,(
    ! [A_1,C_586,D_588] :
      ( u1_struct_0(A_1) = C_586
      | g1_pre_topc(C_586,D_588) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17700])).

tff(c_31466,plain,(
    ! [A_994,A_995] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_994),u1_pre_topc(A_994))) = u1_struct_0(A_995)
      | g1_pre_topc(u1_struct_0(A_994),u1_pre_topc(A_994)) != A_995
      | ~ m1_subset_1(u1_pre_topc(A_995),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_995))))
      | ~ v1_pre_topc(A_995)
      | ~ l1_pre_topc(A_995)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_994),u1_pre_topc(A_994)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_994),u1_pre_topc(A_994)))
      | ~ l1_pre_topc(A_994) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26943,c_17704])).

tff(c_31491,plain,(
    ! [A_996,A_997] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996))) = u1_struct_0(A_997)
      | g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996)) != A_997
      | ~ v1_pre_topc(A_997)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996)))
      | ~ l1_pre_topc(A_996)
      | ~ l1_pre_topc(A_997) ) ),
    inference(resolution,[status(thm)],[c_14,c_31466])).

tff(c_31521,plain,(
    ! [A_996] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996))) = u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_996),u1_pre_topc(A_996)))
      | ~ l1_pre_topc(A_996)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_17687,c_31491])).

tff(c_31542,plain,(
    ! [A_998] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_998),u1_pre_topc(A_998))) = u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_998),u1_pre_topc(A_998)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_998),u1_pre_topc(A_998)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_998),u1_pre_topc(A_998)))
      | ~ l1_pre_topc(A_998) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17694,c_31521])).

tff(c_31583,plain,(
    ! [A_999] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999))) = u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_999),u1_pre_topc(A_999)))
      | ~ l1_pre_topc(A_999) ) ),
    inference(resolution,[status(thm)],[c_63,c_31542])).

tff(c_31624,plain,(
    ! [A_1000] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1000),u1_pre_topc(A_1000))) = u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_1000),u1_pre_topc(A_1000)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_1000) ) ),
    inference(resolution,[status(thm)],[c_69,c_31583])).

tff(c_25901,plain,(
    ! [A_843] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_843),u1_pre_topc(A_843))),u1_pre_topc(A_843)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_843),u1_pre_topc(A_843)))
      | ~ l1_pre_topc(A_843) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25860,c_69])).

tff(c_32257,plain,(
    ! [A_1006] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(A_1006)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1006),u1_pre_topc(A_1006)))
      | ~ l1_pre_topc(A_1006)
      | g1_pre_topc(u1_struct_0(A_1006),u1_pre_topc(A_1006)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_1006) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31624,c_25901])).

tff(c_32287,plain,(
    ! [A_1007] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(A_1007)))
      | g1_pre_topc(u1_struct_0(A_1007),u1_pre_topc(A_1007)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_1007) ) ),
    inference(resolution,[status(thm)],[c_69,c_32257])).

tff(c_32313,plain,(
    ! [A_1] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(A_1)))
      | k1_pre_topc('#skF_1','#skF_3') != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32287])).

tff(c_25904,plain,(
    ! [A_843] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_843),u1_pre_topc(A_843))),u1_pre_topc(A_843)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_843),u1_pre_topc(A_843)))
      | ~ l1_pre_topc(A_843) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25860,c_63])).

tff(c_32394,plain,(
    ! [A_1012] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(A_1012)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1012),u1_pre_topc(A_1012)))
      | ~ l1_pre_topc(A_1012)
      | g1_pre_topc(u1_struct_0(A_1012),u1_pre_topc(A_1012)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_1012) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31624,c_25904])).

tff(c_32397,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32313,c_32394])).

tff(c_32428,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17694,c_17687,c_32397])).

tff(c_32528,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32428])).

tff(c_32534,plain,
    ( ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32528])).

tff(c_32540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17694,c_17687,c_32534])).

tff(c_32542,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32428])).

tff(c_25638,plain,(
    ! [A_825,B_826] :
      ( u1_struct_0(g1_pre_topc(A_825,B_826)) = A_825
      | ~ m1_subset_1(B_826,k1_zfmisc_1(k1_zfmisc_1(A_825)))
      | ~ v1_pre_topc(g1_pre_topc(A_825,B_826))
      | ~ l1_pre_topc(g1_pre_topc(A_825,B_826)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17702])).

tff(c_25648,plain,(
    ! [A_829] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_829),u1_pre_topc(A_829))) = u1_struct_0(A_829)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_829),u1_pre_topc(A_829)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_829),u1_pre_topc(A_829)))
      | ~ l1_pre_topc(A_829) ) ),
    inference(resolution,[status(thm)],[c_14,c_25638])).

tff(c_25656,plain,(
    ! [A_830] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_830),u1_pre_topc(A_830))) = u1_struct_0(A_830)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_830),u1_pre_topc(A_830)))
      | ~ l1_pre_topc(A_830) ) ),
    inference(resolution,[status(thm)],[c_63,c_25648])).

tff(c_25663,plain,(
    ! [A_9] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9))) = u1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_69,c_25656])).

tff(c_25715,plain,(
    ! [A_832,C_833] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_832,C_833)),u1_pre_topc(k1_pre_topc(A_832,C_833))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_832),u1_pre_topc(A_832)),C_833)
      | ~ m1_subset_1(C_833,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_832),u1_pre_topc(A_832)))))
      | ~ m1_subset_1(C_833,k1_zfmisc_1(u1_struct_0(A_832)))
      | ~ l1_pre_topc(A_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_25719,plain,(
    ! [A_9,C_833] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_9,C_833)),u1_pre_topc(k1_pre_topc(A_9,C_833))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9)),C_833)
      | ~ m1_subset_1(C_833,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(C_833,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25663,c_25715])).

tff(c_32817,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32542,c_25719])).

tff(c_33091,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_95,c_95,c_32817])).

tff(c_25664,plain,(
    ! [A_831] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_831),u1_pre_topc(A_831))) = u1_struct_0(A_831)
      | ~ l1_pre_topc(A_831) ) ),
    inference(resolution,[status(thm)],[c_69,c_25656])).

tff(c_26,plain,(
    ! [B_26,A_24] :
      ( v2_compts_1(B_26,A_24)
      | ~ v1_compts_1(k1_pre_topc(A_24,B_26))
      | k1_xboole_0 = B_26
      | ~ v2_pre_topc(A_24)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_25676,plain,(
    ! [B_26,A_831] :
      ( v2_compts_1(B_26,g1_pre_topc(u1_struct_0(A_831),u1_pre_topc(A_831)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_831),u1_pre_topc(A_831)),B_26))
      | k1_xboole_0 = B_26
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_831),u1_pre_topc(A_831)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_831)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_831),u1_pre_topc(A_831)))
      | ~ l1_pre_topc(A_831) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25664,c_26])).

tff(c_33188,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_33091,c_25676])).

tff(c_33262,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_25618,c_33188])).

tff(c_33263,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_25619,c_17714,c_33262])).

tff(c_33305,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_33263])).

tff(c_33311,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_33305])).

tff(c_33317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_33311])).

tff(c_33318,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_33263])).

tff(c_33327,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_33318])).

tff(c_33334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_33327])).

tff(c_33335,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_33344,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_33335])).

tff(c_33486,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_33461,c_33344])).

tff(c_33519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_33486])).

tff(c_33521,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_33335])).

tff(c_33336,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_96,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_134,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_166,plain,(
    ! [A_61,B_62] :
      ( v1_compts_1(k1_pre_topc(A_61,B_62))
      | ~ v2_compts_1(B_62,A_61)
      | k1_xboole_0 = B_62
      | ~ v2_pre_topc(A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_169,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_166])).

tff(c_172,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_71,c_169])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_189,plain,(
    ! [A_64] :
      ( v1_compts_1(k1_pre_topc(A_64,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_64)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_173,c_32])).

tff(c_192,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_189])).

tff(c_195,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71,c_192])).

tff(c_98,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_8])).

tff(c_104,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98])).

tff(c_110,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_113,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_110])).

tff(c_101,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_10])).

tff(c_107,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_127,plain,(
    ! [C_47,A_48,D_49,B_50] :
      ( C_47 = A_48
      | g1_pre_topc(C_47,D_49) != g1_pre_topc(A_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_129,plain,(
    ! [A_1,A_48,B_50] :
      ( u1_struct_0(A_1) = A_48
      | g1_pre_topc(A_48,B_50) != A_1
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_48)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_238,plain,(
    ! [A_79,B_80] :
      ( u1_struct_0(g1_pre_topc(A_79,B_80)) = A_79
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79)))
      | ~ v1_pre_topc(g1_pre_topc(A_79,B_80))
      | ~ l1_pre_topc(g1_pre_topc(A_79,B_80)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_129])).

tff(c_395,plain,(
    ! [A_89] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89))) = u1_struct_0(A_89)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_238])).

tff(c_409,plain,(
    ! [A_90] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_90),u1_pre_topc(A_90))) = u1_struct_0(A_90)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_90),u1_pre_topc(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_63,c_395])).

tff(c_423,plain,(
    ! [A_91] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91))) = u1_struct_0(A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_69,c_409])).

tff(c_1395,plain,(
    ! [A_125] :
      ( g1_pre_topc(u1_struct_0(A_125),u1_pre_topc(g1_pre_topc(u1_struct_0(A_125),u1_pre_topc(A_125)))) = g1_pre_topc(u1_struct_0(A_125),u1_pre_topc(A_125))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_125),u1_pre_topc(A_125)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_125),u1_pre_topc(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_2])).

tff(c_118,plain,(
    ! [D_43,B_44,C_45,A_46] :
      ( D_43 = B_44
      | g1_pre_topc(C_45,D_43) != g1_pre_topc(A_46,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_122,plain,(
    ! [A_1,D_43,C_45] :
      ( u1_pre_topc(A_1) = D_43
      | g1_pre_topc(C_45,D_43) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_5959,plain,(
    ! [A_238,A_239] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_238),u1_pre_topc(A_238))) = u1_pre_topc(A_239)
      | g1_pre_topc(u1_struct_0(A_238),u1_pre_topc(A_238)) != A_239
      | ~ m1_subset_1(u1_pre_topc(A_239),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_239))))
      | ~ v1_pre_topc(A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_238),u1_pre_topc(A_238)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_238),u1_pre_topc(A_238)))
      | ~ l1_pre_topc(A_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_122])).

tff(c_5984,plain,(
    ! [A_240,A_241] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240))) = u1_pre_topc(A_241)
      | g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)) != A_241
      | ~ v1_pre_topc(A_241)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_14,c_5959])).

tff(c_6016,plain,(
    ! [A_240] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_240),u1_pre_topc(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_107,c_5984])).

tff(c_6038,plain,(
    ! [A_242] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_242),u1_pre_topc(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_6016])).

tff(c_6110,plain,(
    ! [A_246] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_246),u1_pre_topc(A_246))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_246),u1_pre_topc(A_246)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_246),u1_pre_topc(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(resolution,[status(thm)],[c_63,c_6038])).

tff(c_6151,plain,(
    ! [A_247] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_247),u1_pre_topc(A_247))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_247),u1_pre_topc(A_247)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_247) ) ),
    inference(resolution,[status(thm)],[c_69,c_6110])).

tff(c_480,plain,(
    ! [A_91] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_69])).

tff(c_6739,plain,(
    ! [A_250] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(A_250)))
      | ~ l1_pre_topc(A_250)
      | g1_pre_topc(u1_struct_0(A_250),u1_pre_topc(A_250)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6151,c_480])).

tff(c_6802,plain,(
    ! [A_254] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_254),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | g1_pre_topc(u1_struct_0(A_254),u1_pre_topc(A_254)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_254) ) ),
    inference(resolution,[status(thm)],[c_69,c_6739])).

tff(c_6828,plain,(
    ! [A_1] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | k1_pre_topc('#skF_1','#skF_3') != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6802])).

tff(c_483,plain,(
    ! [A_91] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_63])).

tff(c_6876,plain,(
    ! [A_256] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(A_256)))
      | ~ l1_pre_topc(A_256)
      | g1_pre_topc(u1_struct_0(A_256),u1_pre_topc(A_256)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6151,c_483])).

tff(c_6879,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6828,c_6876])).

tff(c_6910,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_107,c_6879])).

tff(c_7010,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6910])).

tff(c_7047,plain,
    ( ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7010])).

tff(c_7053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_107,c_7047])).

tff(c_7055,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_6910])).

tff(c_454,plain,(
    ! [A_91,C_23] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_91,C_23)),u1_pre_topc(k1_pre_topc(A_91,C_23))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)),C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_24])).

tff(c_7298,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7055,c_454])).

tff(c_7570,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_95,c_95,c_7298])).

tff(c_176,plain,(
    ! [A_24] :
      ( v2_compts_1('#skF_3',A_24)
      | ~ v1_compts_1(k1_pre_topc(A_24,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_173,c_30])).

tff(c_466,plain,(
    ! [A_91] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_176])).

tff(c_7703,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7570,c_466])).

tff(c_7772,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_195,c_7703])).

tff(c_7773,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_7772])).

tff(c_7795,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_7773])).

tff(c_7801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7795])).

tff(c_7803,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_7802,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_7825,plain,(
    ! [A_270,B_271] :
      ( u1_struct_0(g1_pre_topc(A_270,B_271)) = A_270
      | ~ m1_subset_1(B_271,k1_zfmisc_1(k1_zfmisc_1(A_270)))
      | ~ v1_pre_topc(g1_pre_topc(A_270,B_271))
      | ~ l1_pre_topc(g1_pre_topc(A_270,B_271)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_129])).

tff(c_7931,plain,(
    ! [A_280] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_280),u1_pre_topc(A_280))) = u1_struct_0(A_280)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_280),u1_pre_topc(A_280)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_280),u1_pre_topc(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(resolution,[status(thm)],[c_14,c_7825])).

tff(c_7942,plain,(
    ! [A_281] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_281),u1_pre_topc(A_281))) = u1_struct_0(A_281)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_281),u1_pre_topc(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_63,c_7931])).

tff(c_7953,plain,(
    ! [A_282] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282))) = u1_struct_0(A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_69,c_7942])).

tff(c_9123,plain,(
    ! [A_321] :
      ( g1_pre_topc(u1_struct_0(A_321),u1_pre_topc(g1_pre_topc(u1_struct_0(A_321),u1_pre_topc(A_321)))) = g1_pre_topc(u1_struct_0(A_321),u1_pre_topc(A_321))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_321),u1_pre_topc(A_321)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_321),u1_pre_topc(A_321)))
      | ~ l1_pre_topc(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7953,c_2])).

tff(c_13542,plain,(
    ! [A_430,A_431] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_430),u1_pre_topc(A_430))) = u1_pre_topc(A_431)
      | g1_pre_topc(u1_struct_0(A_430),u1_pre_topc(A_430)) != A_431
      | ~ m1_subset_1(u1_pre_topc(A_431),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_431))))
      | ~ v1_pre_topc(A_431)
      | ~ l1_pre_topc(A_431)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_430),u1_pre_topc(A_430)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_430),u1_pre_topc(A_430)))
      | ~ l1_pre_topc(A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9123,c_122])).

tff(c_13567,plain,(
    ! [A_432,A_433] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432))) = u1_pre_topc(A_433)
      | g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)) != A_433
      | ~ v1_pre_topc(A_433)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)))
      | ~ l1_pre_topc(A_432)
      | ~ l1_pre_topc(A_433) ) ),
    inference(resolution,[status(thm)],[c_14,c_13542])).

tff(c_13599,plain,(
    ! [A_432] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)))
      | ~ l1_pre_topc(A_432)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_107,c_13567])).

tff(c_13621,plain,(
    ! [A_434] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_434),u1_pre_topc(A_434))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_434),u1_pre_topc(A_434)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_434),u1_pre_topc(A_434)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_434),u1_pre_topc(A_434)))
      | ~ l1_pre_topc(A_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_13599])).

tff(c_13693,plain,(
    ! [A_438] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_438),u1_pre_topc(A_438))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_438),u1_pre_topc(A_438)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_438),u1_pre_topc(A_438)))
      | ~ l1_pre_topc(A_438) ) ),
    inference(resolution,[status(thm)],[c_63,c_13621])).

tff(c_13734,plain,(
    ! [A_439] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_439),u1_pre_topc(A_439))) = u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | g1_pre_topc(u1_struct_0(A_439),u1_pre_topc(A_439)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_439) ) ),
    inference(resolution,[status(thm)],[c_69,c_13693])).

tff(c_8010,plain,(
    ! [A_282] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7953,c_69])).

tff(c_14324,plain,(
    ! [A_442] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_442),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_442),u1_pre_topc(A_442)))
      | ~ l1_pre_topc(A_442)
      | g1_pre_topc(u1_struct_0(A_442),u1_pre_topc(A_442)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_442) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13734,c_8010])).

tff(c_14387,plain,(
    ! [A_446] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_446),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | g1_pre_topc(u1_struct_0(A_446),u1_pre_topc(A_446)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_446) ) ),
    inference(resolution,[status(thm)],[c_69,c_14324])).

tff(c_14413,plain,(
    ! [A_1] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | k1_pre_topc('#skF_1','#skF_3') != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14387])).

tff(c_8013,plain,(
    ! [A_282] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7953,c_63])).

tff(c_14461,plain,(
    ! [A_448] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448)))
      | ~ l1_pre_topc(A_448)
      | g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448)) != k1_pre_topc('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13734,c_8013])).

tff(c_14464,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14413,c_14461])).

tff(c_14495,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))))
    | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_107,c_14464])).

tff(c_14595,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14495])).

tff(c_14632,plain,
    ( ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14595])).

tff(c_14638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_107,c_14632])).

tff(c_14640,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14495])).

tff(c_7975,plain,(
    ! [A_282,C_23] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_282,C_23)),u1_pre_topc(k1_pre_topc(A_282,C_23))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)),C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7953,c_24])).

tff(c_14885,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14640,c_7975])).

tff(c_15159,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_95,c_95,c_14885])).

tff(c_7990,plain,(
    ! [B_26,A_282] :
      ( v2_compts_1(B_26,g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)),B_26))
      | k1_xboole_0 = B_26
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7953,c_26])).

tff(c_15257,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15159,c_7990])).

tff(c_15329,plain,
    ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_7802,c_15257])).

tff(c_15330,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7803,c_134,c_15329])).

tff(c_15423,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15330])).

tff(c_15429,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_15423])).

tff(c_15435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_15429])).

tff(c_15436,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15330])).

tff(c_15445,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_15436])).

tff(c_15452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_15445])).

tff(c_15454,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_15549,plain,(
    ! [A_478,B_479] :
      ( u1_struct_0(g1_pre_topc(A_478,B_479)) = A_478
      | ~ m1_subset_1(B_479,k1_zfmisc_1(k1_zfmisc_1(A_478)))
      | ~ v1_pre_topc(g1_pre_topc(A_478,B_479))
      | ~ l1_pre_topc(g1_pre_topc(A_478,B_479)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_129])).

tff(c_15559,plain,(
    ! [A_482] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_482),u1_pre_topc(A_482))) = u1_struct_0(A_482)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_482),u1_pre_topc(A_482)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_482),u1_pre_topc(A_482)))
      | ~ l1_pre_topc(A_482) ) ),
    inference(resolution,[status(thm)],[c_14,c_15549])).

tff(c_15570,plain,(
    ! [A_485] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_485),u1_pre_topc(A_485))) = u1_struct_0(A_485)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_485),u1_pre_topc(A_485)))
      | ~ l1_pre_topc(A_485) ) ),
    inference(resolution,[status(thm)],[c_63,c_15559])).

tff(c_15578,plain,(
    ! [A_486] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_486),u1_pre_topc(A_486))) = u1_struct_0(A_486)
      | ~ l1_pre_topc(A_486) ) ),
    inference(resolution,[status(thm)],[c_69,c_15570])).

tff(c_15453,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_15461,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_15453])).

tff(c_15603,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15578,c_15461])).

tff(c_15636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_15603])).

tff(c_15638,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_15453])).

tff(c_42,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_15714,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15454,c_15638,c_42])).

tff(c_17080,plain,(
    ! [A_557,C_558] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_557,C_558)),u1_pre_topc(k1_pre_topc(A_557,C_558))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_557),u1_pre_topc(A_557)),C_558)
      | ~ m1_subset_1(C_558,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_557),u1_pre_topc(A_557)))))
      | ~ m1_subset_1(C_558,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_17082,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15714,c_17080])).

tff(c_17089,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17082])).

tff(c_17340,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_17089])).

tff(c_15656,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15638,c_10])).

tff(c_15659,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15656])).

tff(c_15665,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_15659])).

tff(c_15671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_15665])).

tff(c_15673,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15656])).

tff(c_17330,plain,(
    ! [A_573,B_574] :
      ( u1_struct_0(g1_pre_topc(A_573,B_574)) = A_573
      | ~ m1_subset_1(B_574,k1_zfmisc_1(k1_zfmisc_1(A_573)))
      | ~ v1_pre_topc(g1_pre_topc(A_573,B_574))
      | ~ l1_pre_topc(g1_pre_topc(A_573,B_574)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_129])).

tff(c_17423,plain,(
    ! [A_581] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_581),u1_pre_topc(A_581))) = u1_struct_0(A_581)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_581),u1_pre_topc(A_581)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_581),u1_pre_topc(A_581)))
      | ~ l1_pre_topc(A_581) ) ),
    inference(resolution,[status(thm)],[c_14,c_17330])).

tff(c_17439,plain,(
    ! [A_582] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_582),u1_pre_topc(A_582))) = u1_struct_0(A_582)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_582),u1_pre_topc(A_582)))
      | ~ l1_pre_topc(A_582) ) ),
    inference(resolution,[status(thm)],[c_63,c_17423])).

tff(c_17448,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_15673,c_17439])).

tff(c_17459,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17448])).

tff(c_17461,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17459,c_15714])).

tff(c_17464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17340,c_17461])).

tff(c_17466,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_17089])).

tff(c_17472,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17466,c_26])).

tff(c_17483,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_17472])).

tff(c_17484,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_17483])).

tff(c_17503,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17484])).

tff(c_17474,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17466,c_8])).

tff(c_17487,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17474])).

tff(c_17499,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17487,c_12])).

tff(c_17502,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17499])).

tff(c_17477,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17466,c_10])).

tff(c_17490,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17477])).

tff(c_17465,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_17089])).

tff(c_17534,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17465,c_2])).

tff(c_17555,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17502,c_17490,c_17534])).

tff(c_15637,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15453])).

tff(c_15763,plain,(
    ! [A_495,B_496] :
      ( v1_compts_1(k1_pre_topc(A_495,B_496))
      | ~ v2_compts_1(B_496,A_495)
      | k1_xboole_0 = B_496
      | ~ v2_pre_topc(A_495)
      | ~ m1_subset_1(B_496,k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ l1_pre_topc(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15766,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15714,c_15763])).

tff(c_15775,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15673,c_15637,c_15766])).

tff(c_17157,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15775])).

tff(c_17160,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_17157])).

tff(c_17167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_17160])).

tff(c_17168,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_15775])).

tff(c_17175,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17168])).

tff(c_17564,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17555,c_17175])).

tff(c_17569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17503,c_17564])).

tff(c_17571,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17484])).

tff(c_17570,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17484])).

tff(c_17581,plain,(
    ! [A_583] :
      ( v2_compts_1('#skF_2',A_583)
      | ~ v1_compts_1(k1_pre_topc(A_583,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ l1_pre_topc(A_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17570,c_17570,c_17570,c_30])).

tff(c_17584,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17466,c_17581])).

tff(c_17590,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17571,c_17584])).

tff(c_17592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_17590])).

tff(c_17594,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17168])).

tff(c_17593,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17168])).

tff(c_17665,plain,(
    ! [A_585] :
      ( v1_compts_1(k1_pre_topc(A_585,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_585)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_585)))
      | ~ l1_pre_topc(A_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17593,c_17593,c_17593,c_32])).

tff(c_17668,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15714,c_17665])).

tff(c_17671,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15673,c_15637,c_17668])).

tff(c_17673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17594,c_17671])).

tff(c_17675,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_33523,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33336,c_17675,c_40])).

tff(c_33524,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_33523])).

tff(c_33543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33521,c_33524])).

tff(c_33544,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_33523])).

tff(c_33560,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_33521,c_10])).

tff(c_33564,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_33560])).

tff(c_33570,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_33564])).

tff(c_33576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_33570])).

tff(c_33578,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_33560])).

tff(c_34023,plain,(
    ! [A_1079,B_1080] :
      ( u1_pre_topc(g1_pre_topc(A_1079,B_1080)) = B_1080
      | ~ m1_subset_1(B_1080,k1_zfmisc_1(k1_zfmisc_1(A_1079)))
      | ~ v1_pre_topc(g1_pre_topc(A_1079,B_1080))
      | ~ l1_pre_topc(g1_pre_topc(A_1079,B_1080)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17711])).

tff(c_34114,plain,(
    ! [A_1087] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1087),u1_pre_topc(A_1087))) = u1_pre_topc(A_1087)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1087),u1_pre_topc(A_1087)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1087),u1_pre_topc(A_1087)))
      | ~ l1_pre_topc(A_1087) ) ),
    inference(resolution,[status(thm)],[c_14,c_34023])).

tff(c_34130,plain,(
    ! [A_1088] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1088),u1_pre_topc(A_1088))) = u1_pre_topc(A_1088)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1088),u1_pre_topc(A_1088)))
      | ~ l1_pre_topc(A_1088) ) ),
    inference(resolution,[status(thm)],[c_63,c_34114])).

tff(c_34139,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33578,c_34130])).

tff(c_34150,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34139])).

tff(c_34185,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34150,c_14])).

tff(c_34212,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33578,c_34185])).

tff(c_34506,plain,(
    ! [C_1094,D_1095] :
      ( u1_struct_0(g1_pre_topc(C_1094,D_1095)) = C_1094
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1094,D_1095)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1094,D_1095)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1094,D_1095))
      | ~ l1_pre_topc(g1_pre_topc(C_1094,D_1095)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17704])).

tff(c_34515,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34150,c_34506])).

tff(c_34540,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33578,c_34212,c_34515])).

tff(c_34574,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_34540])).

tff(c_34580,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_34574])).

tff(c_34586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34580])).

tff(c_34587,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_34540])).

tff(c_33580,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33336,c_33521,c_42])).

tff(c_34626,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34587,c_33580])).

tff(c_34636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33544,c_34626])).

tff(c_34638,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_34645,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34638,c_46])).

tff(c_34646,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34645])).

tff(c_48,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34656,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_34638,c_48])).

tff(c_34816,plain,(
    ! [A_1128,C_1129] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_1128,C_1129)),u1_pre_topc(k1_pre_topc(A_1128,C_1129))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_1128),u1_pre_topc(A_1128)),C_1129)
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1128),u1_pre_topc(A_1128)))))
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(u1_struct_0(A_1128)))
      | ~ l1_pre_topc(A_1128) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34818,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34656,c_34816])).

tff(c_34823,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34818])).

tff(c_34824,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_34823])).

tff(c_34666,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34656,c_10])).

tff(c_34680,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_34666])).

tff(c_34686,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_34680])).

tff(c_34692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34686])).

tff(c_34694,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34666])).

tff(c_34651,plain,(
    ! [C_1098,A_1099,D_1100,B_1101] :
      ( C_1098 = A_1099
      | g1_pre_topc(C_1098,D_1100) != g1_pre_topc(A_1099,B_1101)
      | ~ m1_subset_1(B_1101,k1_zfmisc_1(k1_zfmisc_1(A_1099))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34653,plain,(
    ! [A_1,A_1099,B_1101] :
      ( u1_struct_0(A_1) = A_1099
      | g1_pre_topc(A_1099,B_1101) != A_1
      | ~ m1_subset_1(B_1101,k1_zfmisc_1(k1_zfmisc_1(A_1099)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_34651])).

tff(c_34761,plain,(
    ! [A_1126,B_1127] :
      ( u1_struct_0(g1_pre_topc(A_1126,B_1127)) = A_1126
      | ~ m1_subset_1(B_1127,k1_zfmisc_1(k1_zfmisc_1(A_1126)))
      | ~ v1_pre_topc(g1_pre_topc(A_1126,B_1127))
      | ~ l1_pre_topc(g1_pre_topc(A_1126,B_1127)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_34653])).

tff(c_34825,plain,(
    ! [A_1130] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1130),u1_pre_topc(A_1130))) = u1_struct_0(A_1130)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1130),u1_pre_topc(A_1130)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1130),u1_pre_topc(A_1130)))
      | ~ l1_pre_topc(A_1130) ) ),
    inference(resolution,[status(thm)],[c_14,c_34761])).

tff(c_34841,plain,(
    ! [A_1132] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))) = u1_struct_0(A_1132)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132)))
      | ~ l1_pre_topc(A_1132) ) ),
    inference(resolution,[status(thm)],[c_63,c_34825])).

tff(c_34844,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34694,c_34841])).

tff(c_34853,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34844])).

tff(c_34855,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34853,c_34656])).

tff(c_34857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34824,c_34855])).

tff(c_34859,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34823])).

tff(c_34862,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34859,c_26])).

tff(c_34873,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_34862])).

tff(c_34874,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34646,c_34873])).

tff(c_34934,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34874])).

tff(c_34867,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34859,c_8])).

tff(c_34880,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34867])).

tff(c_34886,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34880,c_12])).

tff(c_34889,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34886])).

tff(c_34870,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34859,c_10])).

tff(c_34883,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34870])).

tff(c_34858,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_34823])).

tff(c_34914,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34858,c_2])).

tff(c_34928,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34883,c_34914])).

tff(c_34939,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34889,c_34928])).

tff(c_34637,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_34695,plain,(
    ! [A_1108,B_1109] :
      ( v1_compts_1(k1_pre_topc(A_1108,B_1109))
      | ~ v2_compts_1(B_1109,A_1108)
      | k1_xboole_0 = B_1109
      | ~ v2_pre_topc(A_1108)
      | ~ m1_subset_1(B_1109,k1_zfmisc_1(u1_struct_0(A_1108)))
      | ~ l1_pre_topc(A_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34698,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34656,c_34695])).

tff(c_34701,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34637,c_34698])).

tff(c_34791,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34694,c_34701])).

tff(c_34792,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_34791])).

tff(c_34795,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_34792])).

tff(c_34802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_34795])).

tff(c_34803,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34791])).

tff(c_34810,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34803])).

tff(c_34941,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34939,c_34810])).

tff(c_34946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34934,c_34941])).

tff(c_34948,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34874])).

tff(c_34947,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34874])).

tff(c_35104,plain,(
    ! [A_1135] :
      ( v2_compts_1('#skF_2',A_1135)
      | ~ v1_compts_1(k1_pre_topc(A_1135,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1135)))
      | ~ l1_pre_topc(A_1135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34947,c_34947,c_34947,c_30])).

tff(c_35107,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34859,c_35104])).

tff(c_35113,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34948,c_35107])).

tff(c_35115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34646,c_35113])).

tff(c_35117,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34803])).

tff(c_35116,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34803])).

tff(c_35131,plain,(
    ! [A_1136] :
      ( v1_compts_1(k1_pre_topc(A_1136,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_1136)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1136)))
      | ~ l1_pre_topc(A_1136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35116,c_35116,c_35116,c_32])).

tff(c_35134,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34656,c_35131])).

tff(c_35137,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34694,c_34637,c_35134])).

tff(c_35139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35117,c_35137])).

tff(c_35140,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34645])).

tff(c_35160,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_34638,c_48])).

tff(c_35170,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_35160,c_10])).

tff(c_35176,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35170])).

tff(c_35182,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_35176])).

tff(c_35188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35182])).

tff(c_35190,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_35170])).

tff(c_35155,plain,(
    ! [D_1141,B_1142,C_1143,A_1144] :
      ( D_1141 = B_1142
      | g1_pre_topc(C_1143,D_1141) != g1_pre_topc(A_1144,B_1142)
      | ~ m1_subset_1(B_1142,k1_zfmisc_1(k1_zfmisc_1(A_1144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_35157,plain,(
    ! [A_1,B_1142,A_1144] :
      ( u1_pre_topc(A_1) = B_1142
      | g1_pre_topc(A_1144,B_1142) != A_1
      | ~ m1_subset_1(B_1142,k1_zfmisc_1(k1_zfmisc_1(A_1144)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_35155])).

tff(c_35279,plain,(
    ! [A_1163,B_1164] :
      ( u1_pre_topc(g1_pre_topc(A_1163,B_1164)) = B_1164
      | ~ m1_subset_1(B_1164,k1_zfmisc_1(k1_zfmisc_1(A_1163)))
      | ~ v1_pre_topc(g1_pre_topc(A_1163,B_1164))
      | ~ l1_pre_topc(g1_pre_topc(A_1163,B_1164)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_35157])).

tff(c_35312,plain,(
    ! [A_1167] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1167),u1_pre_topc(A_1167))) = u1_pre_topc(A_1167)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1167),u1_pre_topc(A_1167)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1167),u1_pre_topc(A_1167)))
      | ~ l1_pre_topc(A_1167) ) ),
    inference(resolution,[status(thm)],[c_14,c_35279])).

tff(c_35328,plain,(
    ! [A_1170] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170))) = u1_pre_topc(A_1170)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170)))
      | ~ l1_pre_topc(A_1170) ) ),
    inference(resolution,[status(thm)],[c_63,c_35312])).

tff(c_35331,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35190,c_35328])).

tff(c_35340,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35331])).

tff(c_35362,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35340,c_14])).

tff(c_35381,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35190,c_35362])).

tff(c_35353,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35340,c_2])).

tff(c_35375,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35190,c_35353])).

tff(c_35584,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35375])).

tff(c_35590,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_35584])).

tff(c_35596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35590])).

tff(c_35597,plain,(
    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_35375])).

tff(c_22,plain,(
    ! [C_15,A_11,D_16,B_12] :
      ( C_15 = A_11
      | g1_pre_topc(C_15,D_16) != g1_pre_topc(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_35635,plain,(
    ! [C_15,D_16] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_15
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_15,D_16)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35597,c_22])).

tff(c_35648,plain,(
    ! [C_15,D_16] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_15
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_15,D_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35381,c_35635])).

tff(c_35746,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_35648])).

tff(c_35764,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35746,c_35160])).

tff(c_35766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35140,c_35764])).

tff(c_35768,plain,(
    ~ v2_compts_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_35794,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_35768,c_52])).

tff(c_35795,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_35794])).

tff(c_54,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_35799,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_35768,c_54])).

tff(c_35809,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_35799,c_10])).

tff(c_35834,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35809])).

tff(c_35840,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_35834])).

tff(c_35846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35840])).

tff(c_35848,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_35809])).

tff(c_35816,plain,(
    ! [C_1189,A_1190,D_1191,B_1192] :
      ( C_1189 = A_1190
      | g1_pre_topc(C_1189,D_1191) != g1_pre_topc(A_1190,B_1192)
      | ~ m1_subset_1(B_1192,k1_zfmisc_1(k1_zfmisc_1(A_1190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_35818,plain,(
    ! [A_1,A_1190,B_1192] :
      ( u1_struct_0(A_1) = A_1190
      | g1_pre_topc(A_1190,B_1192) != A_1
      | ~ m1_subset_1(B_1192,k1_zfmisc_1(k1_zfmisc_1(A_1190)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_35816])).

tff(c_35941,plain,(
    ! [A_1217,B_1218] :
      ( u1_struct_0(g1_pre_topc(A_1217,B_1218)) = A_1217
      | ~ m1_subset_1(B_1218,k1_zfmisc_1(k1_zfmisc_1(A_1217)))
      | ~ v1_pre_topc(g1_pre_topc(A_1217,B_1218))
      | ~ l1_pre_topc(g1_pre_topc(A_1217,B_1218)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_35818])).

tff(c_35969,plain,(
    ! [A_1219] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1219),u1_pre_topc(A_1219))) = u1_struct_0(A_1219)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1219),u1_pre_topc(A_1219)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1219),u1_pre_topc(A_1219)))
      | ~ l1_pre_topc(A_1219) ) ),
    inference(resolution,[status(thm)],[c_14,c_35941])).

tff(c_35977,plain,(
    ! [A_1220] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1220),u1_pre_topc(A_1220))) = u1_struct_0(A_1220)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1220),u1_pre_topc(A_1220)))
      | ~ l1_pre_topc(A_1220) ) ),
    inference(resolution,[status(thm)],[c_63,c_35969])).

tff(c_35980,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35848,c_35977])).

tff(c_35989,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35980])).

tff(c_35999,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35989,c_35799])).

tff(c_36078,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35999,c_26])).

tff(c_36089,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_36078])).

tff(c_36090,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_35795,c_36089])).

tff(c_36100,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36090])).

tff(c_36083,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35999,c_8])).

tff(c_36096,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36083])).

tff(c_36103,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36096,c_12])).

tff(c_36106,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36103])).

tff(c_36086,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35999,c_10])).

tff(c_36099,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36086])).

tff(c_35991,plain,(
    ! [A_1221,C_1222] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(A_1221,C_1222)),u1_pre_topc(k1_pre_topc(A_1221,C_1222))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A_1221),u1_pre_topc(A_1221)),C_1222)
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1221),u1_pre_topc(A_1221)))))
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(u1_struct_0(A_1221)))
      | ~ l1_pre_topc(A_1221) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35993,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35799,c_35991])).

tff(c_35998,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35993])).

tff(c_36185,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35999,c_35998])).

tff(c_36210,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36185,c_2])).

tff(c_36230,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') = k1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36106,c_36099,c_36210])).

tff(c_35767,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_35854,plain,(
    ! [A_1199,B_1200] :
      ( v1_compts_1(k1_pre_topc(A_1199,B_1200))
      | ~ v2_compts_1(B_1200,A_1199)
      | k1_xboole_0 = B_1200
      | ~ v2_pre_topc(A_1199)
      | ~ m1_subset_1(B_1200,k1_zfmisc_1(u1_struct_0(A_1199)))
      | ~ l1_pre_topc(A_1199) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_35857,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_35799,c_35854])).

tff(c_35860,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35848,c_35767,c_35857])).

tff(c_35866,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35860])).

tff(c_35872,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_35866])).

tff(c_35878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_35872])).

tff(c_35879,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_35860])).

tff(c_35886,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_35879])).

tff(c_36253,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36230,c_35886])).

tff(c_36257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36100,c_36253])).

tff(c_36259,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36090])).

tff(c_36258,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36090])).

tff(c_37087,plain,(
    ! [A_1244] :
      ( v2_compts_1('#skF_2',A_1244)
      | ~ v1_compts_1(k1_pre_topc(A_1244,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1244)))
      | ~ l1_pre_topc(A_1244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36258,c_36258,c_36258,c_30])).

tff(c_37093,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_35999,c_37087])).

tff(c_37099,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36259,c_37093])).

tff(c_37101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35795,c_37099])).

tff(c_37103,plain,(
    ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_35879])).

tff(c_37102,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_35879])).

tff(c_37124,plain,(
    ! [A_1246] :
      ( v1_compts_1(k1_pre_topc(A_1246,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_1246)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1246)))
      | ~ l1_pre_topc(A_1246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37102,c_37102,c_37102,c_32])).

tff(c_37127,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_35799,c_37124])).

tff(c_37130,plain,(
    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35848,c_35767,c_37127])).

tff(c_37132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37103,c_37130])).

tff(c_37133,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_35794])).

tff(c_37136,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_35768,c_54])).

tff(c_37143,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_37136,c_10])).

tff(c_37175,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_37143])).

tff(c_37181,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_37175])).

tff(c_37187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37181])).

tff(c_37189,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_37143])).

tff(c_37158,plain,(
    ! [C_1251,A_1252,D_1253,B_1254] :
      ( C_1251 = A_1252
      | g1_pre_topc(C_1251,D_1253) != g1_pre_topc(A_1252,B_1254)
      | ~ m1_subset_1(B_1254,k1_zfmisc_1(k1_zfmisc_1(A_1252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37160,plain,(
    ! [A_1,A_1252,B_1254] :
      ( u1_struct_0(A_1) = A_1252
      | g1_pre_topc(A_1252,B_1254) != A_1
      | ~ m1_subset_1(B_1254,k1_zfmisc_1(k1_zfmisc_1(A_1252)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_37158])).

tff(c_37292,plain,(
    ! [A_1281,B_1282] :
      ( u1_struct_0(g1_pre_topc(A_1281,B_1282)) = A_1281
      | ~ m1_subset_1(B_1282,k1_zfmisc_1(k1_zfmisc_1(A_1281)))
      | ~ v1_pre_topc(g1_pre_topc(A_1281,B_1282))
      | ~ l1_pre_topc(g1_pre_topc(A_1281,B_1282)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_37160])).

tff(c_37328,plain,(
    ! [A_1285] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1285),u1_pre_topc(A_1285))) = u1_struct_0(A_1285)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1285),u1_pre_topc(A_1285)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1285),u1_pre_topc(A_1285)))
      | ~ l1_pre_topc(A_1285) ) ),
    inference(resolution,[status(thm)],[c_14,c_37292])).

tff(c_37336,plain,(
    ! [A_1286] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_1286),u1_pre_topc(A_1286))) = u1_struct_0(A_1286)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1286),u1_pre_topc(A_1286)))
      | ~ l1_pre_topc(A_1286) ) ),
    inference(resolution,[status(thm)],[c_63,c_37328])).

tff(c_37339,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_37189,c_37336])).

tff(c_37348,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37339])).

tff(c_37350,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37348,c_37136])).

tff(c_37352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37133,c_37350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.09/8.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.39/8.27  
% 19.39/8.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.39/8.27  %$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 19.39/8.27  
% 19.39/8.27  %Foreground sorts:
% 19.39/8.27  
% 19.39/8.27  
% 19.39/8.27  %Background operators:
% 19.39/8.27  
% 19.39/8.27  
% 19.39/8.27  %Foreground operators:
% 19.39/8.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.39/8.27  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 19.39/8.27  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 19.39/8.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 19.39/8.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.39/8.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 19.39/8.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.39/8.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.39/8.27  tff('#skF_2', type, '#skF_2': $i).
% 19.39/8.27  tff('#skF_3', type, '#skF_3': $i).
% 19.39/8.27  tff('#skF_1', type, '#skF_1': $i).
% 19.39/8.27  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.39/8.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.39/8.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.39/8.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.39/8.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.39/8.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.39/8.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.39/8.27  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 19.39/8.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.39/8.27  
% 19.39/8.32  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_compts_1(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v2_compts_1(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_compts_1)).
% 19.39/8.32  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 19.39/8.32  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 19.39/8.32  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 19.39/8.32  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 19.39/8.32  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 19.39/8.32  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 19.39/8.32  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 19.39/8.32  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 19.39/8.32  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))) => ((B = C) => (g1_pre_topc(u1_struct_0(k1_pre_topc(A, B)), u1_pre_topc(k1_pre_topc(A, B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_pre_topc)).
% 19.39/8.32  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_50, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_95, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_50])).
% 19.39/8.32  tff(c_14, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.39/8.32  tff(c_65, plain, (![A_34, B_35]: (l1_pre_topc(g1_pre_topc(A_34, B_35)) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.39/8.32  tff(c_69, plain, (![A_9]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9))) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_14, c_65])).
% 19.39/8.32  tff(c_59, plain, (![A_31, B_32]: (v1_pre_topc(g1_pre_topc(A_31, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.39/8.32  tff(c_63, plain, (![A_9]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9))) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_14, c_59])).
% 19.39/8.32  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.39/8.32  tff(c_17700, plain, (![C_586, A_587, D_588, B_589]: (C_586=A_587 | g1_pre_topc(C_586, D_588)!=g1_pre_topc(A_587, B_589) | ~m1_subset_1(B_589, k1_zfmisc_1(k1_zfmisc_1(A_587))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.32  tff(c_17702, plain, (![A_1, A_587, B_589]: (u1_struct_0(A_1)=A_587 | g1_pre_topc(A_587, B_589)!=A_1 | ~m1_subset_1(B_589, k1_zfmisc_1(k1_zfmisc_1(A_587))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17700])).
% 19.39/8.32  tff(c_33432, plain, (![A_1040, B_1041]: (u1_struct_0(g1_pre_topc(A_1040, B_1041))=A_1040 | ~m1_subset_1(B_1041, k1_zfmisc_1(k1_zfmisc_1(A_1040))) | ~v1_pre_topc(g1_pre_topc(A_1040, B_1041)) | ~l1_pre_topc(g1_pre_topc(A_1040, B_1041)))), inference(reflexivity, [status(thm), theory('equality')], [c_17702])).
% 19.39/8.32  tff(c_33445, plain, (![A_1046]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1046), u1_pre_topc(A_1046)))=u1_struct_0(A_1046) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1046), u1_pre_topc(A_1046))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1046), u1_pre_topc(A_1046))) | ~l1_pre_topc(A_1046))), inference(resolution, [status(thm)], [c_14, c_33432])).
% 19.39/8.32  tff(c_33453, plain, (![A_1047]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1047), u1_pre_topc(A_1047)))=u1_struct_0(A_1047) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1047), u1_pre_topc(A_1047))) | ~l1_pre_topc(A_1047))), inference(resolution, [status(thm)], [c_63, c_33445])).
% 19.39/8.32  tff(c_33461, plain, (![A_1048]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1048), u1_pre_topc(A_1048)))=u1_struct_0(A_1048) | ~l1_pre_topc(A_1048))), inference(resolution, [status(thm)], [c_69, c_33453])).
% 19.39/8.32  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_16, plain, (![A_10]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_10), u1_pre_topc(A_10))) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.39/8.32  tff(c_44, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_17714, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_44])).
% 19.39/8.32  tff(c_56, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_71, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 19.39/8.32  tff(c_17747, plain, (![A_604, B_605]: (v1_compts_1(k1_pre_topc(A_604, B_605)) | ~v2_compts_1(B_605, A_604) | k1_xboole_0=B_605 | ~v2_pre_topc(A_604) | ~m1_subset_1(B_605, k1_zfmisc_1(u1_struct_0(A_604))) | ~l1_pre_topc(A_604))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_17750, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_17747])).
% 19.39/8.32  tff(c_17753, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_71, c_17750])).
% 19.39/8.32  tff(c_17754, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_17753])).
% 19.39/8.32  tff(c_32, plain, (![A_24]: (v1_compts_1(k1_pre_topc(A_24, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_24) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_17765, plain, (![A_606]: (v1_compts_1(k1_pre_topc(A_606, '#skF_3')) | ~v2_compts_1('#skF_3', A_606) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_606))) | ~l1_pre_topc(A_606))), inference(demodulation, [status(thm), theory('equality')], [c_17754, c_17754, c_17754, c_32])).
% 19.39/8.32  tff(c_17768, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_17765])).
% 19.39/8.32  tff(c_17771, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_71, c_17768])).
% 19.39/8.32  tff(c_8, plain, (![A_4, B_5]: (m1_pre_topc(k1_pre_topc(A_4, B_5), A_4) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.39/8.32  tff(c_17678, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_8])).
% 19.39/8.32  tff(c_17684, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17678])).
% 19.39/8.32  tff(c_12, plain, (![B_8, A_6]: (l1_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.39/8.32  tff(c_17691, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17684, c_12])).
% 19.39/8.32  tff(c_17694, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17691])).
% 19.39/8.32  tff(c_10, plain, (![A_4, B_5]: (v1_pre_topc(k1_pre_topc(A_4, B_5)) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.39/8.32  tff(c_17681, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_10])).
% 19.39/8.32  tff(c_17687, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17681])).
% 19.39/8.32  tff(c_17821, plain, (![A_622, B_623]: (u1_struct_0(g1_pre_topc(A_622, B_623))=A_622 | ~m1_subset_1(B_623, k1_zfmisc_1(k1_zfmisc_1(A_622))) | ~v1_pre_topc(g1_pre_topc(A_622, B_623)) | ~l1_pre_topc(g1_pre_topc(A_622, B_623)))), inference(reflexivity, [status(thm), theory('equality')], [c_17702])).
% 19.39/8.32  tff(c_17978, plain, (![A_632]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_632), u1_pre_topc(A_632)))=u1_struct_0(A_632) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_632), u1_pre_topc(A_632))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_632), u1_pre_topc(A_632))) | ~l1_pre_topc(A_632))), inference(resolution, [status(thm)], [c_14, c_17821])).
% 19.39/8.32  tff(c_17992, plain, (![A_633]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_633), u1_pre_topc(A_633)))=u1_struct_0(A_633) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_633), u1_pre_topc(A_633))) | ~l1_pre_topc(A_633))), inference(resolution, [status(thm)], [c_63, c_17978])).
% 19.39/8.32  tff(c_18006, plain, (![A_634]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634)))=u1_struct_0(A_634) | ~l1_pre_topc(A_634))), inference(resolution, [status(thm)], [c_69, c_17992])).
% 19.39/8.32  tff(c_18978, plain, (![A_668]: (g1_pre_topc(u1_struct_0(A_668), u1_pre_topc(g1_pre_topc(u1_struct_0(A_668), u1_pre_topc(A_668))))=g1_pre_topc(u1_struct_0(A_668), u1_pre_topc(A_668)) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_668), u1_pre_topc(A_668))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_668), u1_pre_topc(A_668))) | ~l1_pre_topc(A_668))), inference(superposition, [status(thm), theory('equality')], [c_18006, c_2])).
% 19.39/8.32  tff(c_17709, plain, (![D_590, B_591, C_592, A_593]: (D_590=B_591 | g1_pre_topc(C_592, D_590)!=g1_pre_topc(A_593, B_591) | ~m1_subset_1(B_591, k1_zfmisc_1(k1_zfmisc_1(A_593))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.32  tff(c_17713, plain, (![A_1, D_590, C_592]: (u1_pre_topc(A_1)=D_590 | g1_pre_topc(C_592, D_590)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17709])).
% 19.39/8.32  tff(c_23765, plain, (![A_795, A_796]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_795), u1_pre_topc(A_795)))=u1_pre_topc(A_796) | g1_pre_topc(u1_struct_0(A_795), u1_pre_topc(A_795))!=A_796 | ~m1_subset_1(u1_pre_topc(A_796), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_796)))) | ~v1_pre_topc(A_796) | ~l1_pre_topc(A_796) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_795), u1_pre_topc(A_795))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_795), u1_pre_topc(A_795))) | ~l1_pre_topc(A_795))), inference(superposition, [status(thm), theory('equality')], [c_18978, c_17713])).
% 19.39/8.32  tff(c_23790, plain, (![A_797, A_798]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797)))=u1_pre_topc(A_798) | g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797))!=A_798 | ~v1_pre_topc(A_798) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797))) | ~l1_pre_topc(A_797) | ~l1_pre_topc(A_798))), inference(resolution, [status(thm)], [c_14, c_23765])).
% 19.39/8.32  tff(c_23822, plain, (![A_797]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_797), u1_pre_topc(A_797))) | ~l1_pre_topc(A_797) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_17687, c_23790])).
% 19.39/8.32  tff(c_23844, plain, (![A_799]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_799), u1_pre_topc(A_799)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_799), u1_pre_topc(A_799))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_799), u1_pre_topc(A_799))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_799), u1_pre_topc(A_799))) | ~l1_pre_topc(A_799))), inference(demodulation, [status(thm), theory('equality')], [c_17694, c_23822])).
% 19.39/8.32  tff(c_23885, plain, (![A_800]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_800), u1_pre_topc(A_800)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_800), u1_pre_topc(A_800))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_800), u1_pre_topc(A_800))) | ~l1_pre_topc(A_800))), inference(resolution, [status(thm)], [c_63, c_23844])).
% 19.39/8.32  tff(c_23926, plain, (![A_801]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_801), u1_pre_topc(A_801)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_801), u1_pre_topc(A_801))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_801))), inference(resolution, [status(thm)], [c_69, c_23885])).
% 19.39/8.32  tff(c_18063, plain, (![A_634]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634))) | ~l1_pre_topc(A_634))), inference(superposition, [status(thm), theory('equality')], [c_18006, c_69])).
% 19.39/8.32  tff(c_24549, plain, (![A_807]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_807), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_807), u1_pre_topc(A_807))) | ~l1_pre_topc(A_807) | g1_pre_topc(u1_struct_0(A_807), u1_pre_topc(A_807))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_807))), inference(superposition, [status(thm), theory('equality')], [c_23926, c_18063])).
% 19.39/8.32  tff(c_24579, plain, (![A_808]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_808), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(A_808), u1_pre_topc(A_808))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_808))), inference(resolution, [status(thm)], [c_69, c_24549])).
% 19.39/8.32  tff(c_24605, plain, (![A_1]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | k1_pre_topc('#skF_1', '#skF_3')!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_24579])).
% 19.39/8.32  tff(c_18066, plain, (![A_634]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634))) | ~l1_pre_topc(A_634))), inference(superposition, [status(thm), theory('equality')], [c_18006, c_63])).
% 19.39/8.32  tff(c_24653, plain, (![A_810]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_810), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_810), u1_pre_topc(A_810))) | ~l1_pre_topc(A_810) | g1_pre_topc(u1_struct_0(A_810), u1_pre_topc(A_810))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_810))), inference(superposition, [status(thm), theory('equality')], [c_23926, c_18066])).
% 19.39/8.32  tff(c_24656, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24605, c_24653])).
% 19.39/8.32  tff(c_24687, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17694, c_17687, c_24656])).
% 19.39/8.32  tff(c_24818, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_24687])).
% 19.39/8.32  tff(c_24824, plain, (~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_24818])).
% 19.39/8.32  tff(c_24830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17694, c_17687, c_24824])).
% 19.39/8.32  tff(c_24832, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24687])).
% 19.39/8.32  tff(c_24, plain, (![A_17, C_23]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_17, C_23)), u1_pre_topc(k1_pre_topc(A_17, C_23)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17)), C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17))))) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.39/8.32  tff(c_18037, plain, (![A_634, C_23]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_634, C_23)), u1_pre_topc(k1_pre_topc(A_634, C_23)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634)), C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_634))) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(A_634) | ~l1_pre_topc(A_634))), inference(superposition, [status(thm), theory('equality')], [c_18006, c_24])).
% 19.39/8.32  tff(c_25079, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24832, c_18037])).
% 19.39/8.32  tff(c_25355, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_95, c_95, c_25079])).
% 19.39/8.32  tff(c_30, plain, (![A_24]: (v2_compts_1(k1_xboole_0, A_24) | ~v1_compts_1(k1_pre_topc(A_24, k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_17760, plain, (![A_24]: (v2_compts_1('#skF_3', A_24) | ~v1_compts_1(k1_pre_topc(A_24, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_17754, c_17754, c_17754, c_30])).
% 19.39/8.32  tff(c_18046, plain, (![A_634]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634)), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_634), u1_pre_topc(A_634))) | ~l1_pre_topc(A_634))), inference(superposition, [status(thm), theory('equality')], [c_18006, c_17760])).
% 19.39/8.32  tff(c_25490, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25355, c_18046])).
% 19.39/8.32  tff(c_25561, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_17771, c_25490])).
% 19.39/8.32  tff(c_25562, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_17714, c_25561])).
% 19.39/8.32  tff(c_25611, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_25562])).
% 19.39/8.32  tff(c_25617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_25611])).
% 19.39/8.32  tff(c_25619, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_17753])).
% 19.39/8.32  tff(c_25618, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_17753])).
% 19.39/8.32  tff(c_17711, plain, (![A_1, B_591, A_593]: (u1_pre_topc(A_1)=B_591 | g1_pre_topc(A_593, B_591)!=A_1 | ~m1_subset_1(B_591, k1_zfmisc_1(k1_zfmisc_1(A_593))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17709])).
% 19.39/8.32  tff(c_25643, plain, (![A_827, B_828]: (u1_pre_topc(g1_pre_topc(A_827, B_828))=B_828 | ~m1_subset_1(B_828, k1_zfmisc_1(k1_zfmisc_1(A_827))) | ~v1_pre_topc(g1_pre_topc(A_827, B_828)) | ~l1_pre_topc(g1_pre_topc(A_827, B_828)))), inference(reflexivity, [status(thm), theory('equality')], [c_17711])).
% 19.39/8.32  tff(c_25775, plain, (![A_839]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_839), u1_pre_topc(A_839)))=u1_pre_topc(A_839) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_839), u1_pre_topc(A_839))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_839), u1_pre_topc(A_839))) | ~l1_pre_topc(A_839))), inference(resolution, [status(thm)], [c_14, c_25643])).
% 19.39/8.32  tff(c_25846, plain, (![A_842]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_842), u1_pre_topc(A_842)))=u1_pre_topc(A_842) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_842), u1_pre_topc(A_842))) | ~l1_pre_topc(A_842))), inference(resolution, [status(thm)], [c_63, c_25775])).
% 19.39/8.32  tff(c_25860, plain, (![A_843]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_843), u1_pre_topc(A_843)))=u1_pre_topc(A_843) | ~l1_pre_topc(A_843))), inference(resolution, [status(thm)], [c_69, c_25846])).
% 19.39/8.32  tff(c_26943, plain, (![A_879]: (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_879), u1_pre_topc(A_879))), u1_pre_topc(A_879))=g1_pre_topc(u1_struct_0(A_879), u1_pre_topc(A_879)) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_879), u1_pre_topc(A_879))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_879), u1_pre_topc(A_879))) | ~l1_pre_topc(A_879))), inference(superposition, [status(thm), theory('equality')], [c_25860, c_2])).
% 19.39/8.32  tff(c_17704, plain, (![A_1, C_586, D_588]: (u1_struct_0(A_1)=C_586 | g1_pre_topc(C_586, D_588)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17700])).
% 19.39/8.32  tff(c_31466, plain, (![A_994, A_995]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_994), u1_pre_topc(A_994)))=u1_struct_0(A_995) | g1_pre_topc(u1_struct_0(A_994), u1_pre_topc(A_994))!=A_995 | ~m1_subset_1(u1_pre_topc(A_995), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_995)))) | ~v1_pre_topc(A_995) | ~l1_pre_topc(A_995) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_994), u1_pre_topc(A_994))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_994), u1_pre_topc(A_994))) | ~l1_pre_topc(A_994))), inference(superposition, [status(thm), theory('equality')], [c_26943, c_17704])).
% 19.39/8.32  tff(c_31491, plain, (![A_996, A_997]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996)))=u1_struct_0(A_997) | g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996))!=A_997 | ~v1_pre_topc(A_997) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996))) | ~l1_pre_topc(A_996) | ~l1_pre_topc(A_997))), inference(resolution, [status(thm)], [c_14, c_31466])).
% 19.39/8.32  tff(c_31521, plain, (![A_996]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996)))=u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_996), u1_pre_topc(A_996))) | ~l1_pre_topc(A_996) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_17687, c_31491])).
% 19.39/8.32  tff(c_31542, plain, (![A_998]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_998), u1_pre_topc(A_998)))=u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_998), u1_pre_topc(A_998))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_998), u1_pre_topc(A_998))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_998), u1_pre_topc(A_998))) | ~l1_pre_topc(A_998))), inference(demodulation, [status(thm), theory('equality')], [c_17694, c_31521])).
% 19.39/8.32  tff(c_31583, plain, (![A_999]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999)))=u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_999), u1_pre_topc(A_999))) | ~l1_pre_topc(A_999))), inference(resolution, [status(thm)], [c_63, c_31542])).
% 19.39/8.32  tff(c_31624, plain, (![A_1000]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1000), u1_pre_topc(A_1000)))=u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_1000), u1_pre_topc(A_1000))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_1000))), inference(resolution, [status(thm)], [c_69, c_31583])).
% 19.39/8.32  tff(c_25901, plain, (![A_843]: (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_843), u1_pre_topc(A_843))), u1_pre_topc(A_843))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_843), u1_pre_topc(A_843))) | ~l1_pre_topc(A_843))), inference(superposition, [status(thm), theory('equality')], [c_25860, c_69])).
% 19.39/8.32  tff(c_32257, plain, (![A_1006]: (l1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(A_1006))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1006), u1_pre_topc(A_1006))) | ~l1_pre_topc(A_1006) | g1_pre_topc(u1_struct_0(A_1006), u1_pre_topc(A_1006))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_1006))), inference(superposition, [status(thm), theory('equality')], [c_31624, c_25901])).
% 19.39/8.32  tff(c_32287, plain, (![A_1007]: (l1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(A_1007))) | g1_pre_topc(u1_struct_0(A_1007), u1_pre_topc(A_1007))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_1007))), inference(resolution, [status(thm)], [c_69, c_32257])).
% 19.39/8.32  tff(c_32313, plain, (![A_1]: (l1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(A_1))) | k1_pre_topc('#skF_1', '#skF_3')!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_32287])).
% 19.39/8.32  tff(c_25904, plain, (![A_843]: (v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_843), u1_pre_topc(A_843))), u1_pre_topc(A_843))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_843), u1_pre_topc(A_843))) | ~l1_pre_topc(A_843))), inference(superposition, [status(thm), theory('equality')], [c_25860, c_63])).
% 19.39/8.32  tff(c_32394, plain, (![A_1012]: (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(A_1012))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1012), u1_pre_topc(A_1012))) | ~l1_pre_topc(A_1012) | g1_pre_topc(u1_struct_0(A_1012), u1_pre_topc(A_1012))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_1012))), inference(superposition, [status(thm), theory('equality')], [c_31624, c_25904])).
% 19.39/8.32  tff(c_32397, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32313, c_32394])).
% 19.39/8.32  tff(c_32428, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17694, c_17687, c_32397])).
% 19.39/8.32  tff(c_32528, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_32428])).
% 19.39/8.32  tff(c_32534, plain, (~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_32528])).
% 19.39/8.32  tff(c_32540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17694, c_17687, c_32534])).
% 19.39/8.32  tff(c_32542, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32428])).
% 19.39/8.32  tff(c_25638, plain, (![A_825, B_826]: (u1_struct_0(g1_pre_topc(A_825, B_826))=A_825 | ~m1_subset_1(B_826, k1_zfmisc_1(k1_zfmisc_1(A_825))) | ~v1_pre_topc(g1_pre_topc(A_825, B_826)) | ~l1_pre_topc(g1_pre_topc(A_825, B_826)))), inference(reflexivity, [status(thm), theory('equality')], [c_17702])).
% 19.39/8.32  tff(c_25648, plain, (![A_829]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_829), u1_pre_topc(A_829)))=u1_struct_0(A_829) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_829), u1_pre_topc(A_829))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_829), u1_pre_topc(A_829))) | ~l1_pre_topc(A_829))), inference(resolution, [status(thm)], [c_14, c_25638])).
% 19.39/8.32  tff(c_25656, plain, (![A_830]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_830), u1_pre_topc(A_830)))=u1_struct_0(A_830) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_830), u1_pre_topc(A_830))) | ~l1_pre_topc(A_830))), inference(resolution, [status(thm)], [c_63, c_25648])).
% 19.39/8.32  tff(c_25663, plain, (![A_9]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9)))=u1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_69, c_25656])).
% 19.39/8.32  tff(c_25715, plain, (![A_832, C_833]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_832, C_833)), u1_pre_topc(k1_pre_topc(A_832, C_833)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_832), u1_pre_topc(A_832)), C_833) | ~m1_subset_1(C_833, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_832), u1_pre_topc(A_832))))) | ~m1_subset_1(C_833, k1_zfmisc_1(u1_struct_0(A_832))) | ~l1_pre_topc(A_832))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.39/8.32  tff(c_25719, plain, (![A_9, C_833]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_9, C_833)), u1_pre_topc(k1_pre_topc(A_9, C_833)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9)), C_833) | ~m1_subset_1(C_833, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(C_833, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~l1_pre_topc(A_9))), inference(superposition, [status(thm), theory('equality')], [c_25663, c_25715])).
% 19.39/8.32  tff(c_32817, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32542, c_25719])).
% 19.39/8.32  tff(c_33091, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_95, c_95, c_32817])).
% 19.39/8.32  tff(c_25664, plain, (![A_831]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_831), u1_pre_topc(A_831)))=u1_struct_0(A_831) | ~l1_pre_topc(A_831))), inference(resolution, [status(thm)], [c_69, c_25656])).
% 19.39/8.32  tff(c_26, plain, (![B_26, A_24]: (v2_compts_1(B_26, A_24) | ~v1_compts_1(k1_pre_topc(A_24, B_26)) | k1_xboole_0=B_26 | ~v2_pre_topc(A_24) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_25676, plain, (![B_26, A_831]: (v2_compts_1(B_26, g1_pre_topc(u1_struct_0(A_831), u1_pre_topc(A_831))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_831), u1_pre_topc(A_831)), B_26)) | k1_xboole_0=B_26 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_831), u1_pre_topc(A_831))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_831))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_831), u1_pre_topc(A_831))) | ~l1_pre_topc(A_831))), inference(superposition, [status(thm), theory('equality')], [c_25664, c_26])).
% 19.39/8.32  tff(c_33188, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_33091, c_25676])).
% 19.39/8.32  tff(c_33262, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_25618, c_33188])).
% 19.39/8.32  tff(c_33263, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_25619, c_17714, c_33262])).
% 19.39/8.32  tff(c_33305, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_33263])).
% 19.39/8.32  tff(c_33311, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_33305])).
% 19.39/8.32  tff(c_33317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_33311])).
% 19.39/8.32  tff(c_33318, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_33263])).
% 19.39/8.32  tff(c_33327, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_33318])).
% 19.39/8.32  tff(c_33334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_33327])).
% 19.39/8.32  tff(c_33335, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 19.39/8.32  tff(c_33344, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_33335])).
% 19.39/8.32  tff(c_33486, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_33461, c_33344])).
% 19.39/8.32  tff(c_33519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_33486])).
% 19.39/8.32  tff(c_33521, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_33335])).
% 19.39/8.32  tff(c_33336, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 19.39/8.32  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_96, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 19.39/8.32  tff(c_134, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_44])).
% 19.39/8.32  tff(c_166, plain, (![A_61, B_62]: (v1_compts_1(k1_pre_topc(A_61, B_62)) | ~v2_compts_1(B_62, A_61) | k1_xboole_0=B_62 | ~v2_pre_topc(A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_169, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_166])).
% 19.39/8.32  tff(c_172, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_71, c_169])).
% 19.39/8.32  tff(c_173, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_172])).
% 19.39/8.32  tff(c_189, plain, (![A_64]: (v1_compts_1(k1_pre_topc(A_64, '#skF_3')) | ~v2_compts_1('#skF_3', A_64) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_173, c_32])).
% 19.39/8.32  tff(c_192, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_189])).
% 19.39/8.32  tff(c_195, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_71, c_192])).
% 19.39/8.32  tff(c_98, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_8])).
% 19.39/8.32  tff(c_104, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98])).
% 19.39/8.32  tff(c_110, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_104, c_12])).
% 19.39/8.32  tff(c_113, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_110])).
% 19.39/8.32  tff(c_101, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_10])).
% 19.39/8.32  tff(c_107, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_101])).
% 19.39/8.32  tff(c_127, plain, (![C_47, A_48, D_49, B_50]: (C_47=A_48 | g1_pre_topc(C_47, D_49)!=g1_pre_topc(A_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.32  tff(c_129, plain, (![A_1, A_48, B_50]: (u1_struct_0(A_1)=A_48 | g1_pre_topc(A_48, B_50)!=A_1 | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_48))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 19.39/8.32  tff(c_238, plain, (![A_79, B_80]: (u1_struct_0(g1_pre_topc(A_79, B_80))=A_79 | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))) | ~v1_pre_topc(g1_pre_topc(A_79, B_80)) | ~l1_pre_topc(g1_pre_topc(A_79, B_80)))), inference(reflexivity, [status(thm), theory('equality')], [c_129])).
% 19.39/8.32  tff(c_395, plain, (![A_89]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89)))=u1_struct_0(A_89) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_14, c_238])).
% 19.39/8.32  tff(c_409, plain, (![A_90]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90)))=u1_struct_0(A_90) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90))) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_63, c_395])).
% 19.39/8.32  tff(c_423, plain, (![A_91]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91)))=u1_struct_0(A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_69, c_409])).
% 19.39/8.32  tff(c_1395, plain, (![A_125]: (g1_pre_topc(u1_struct_0(A_125), u1_pre_topc(g1_pre_topc(u1_struct_0(A_125), u1_pre_topc(A_125))))=g1_pre_topc(u1_struct_0(A_125), u1_pre_topc(A_125)) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_125), u1_pre_topc(A_125))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_125), u1_pre_topc(A_125))) | ~l1_pre_topc(A_125))), inference(superposition, [status(thm), theory('equality')], [c_423, c_2])).
% 19.39/8.32  tff(c_118, plain, (![D_43, B_44, C_45, A_46]: (D_43=B_44 | g1_pre_topc(C_45, D_43)!=g1_pre_topc(A_46, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.32  tff(c_122, plain, (![A_1, D_43, C_45]: (u1_pre_topc(A_1)=D_43 | g1_pre_topc(C_45, D_43)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 19.39/8.32  tff(c_5959, plain, (![A_238, A_239]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_238), u1_pre_topc(A_238)))=u1_pre_topc(A_239) | g1_pre_topc(u1_struct_0(A_238), u1_pre_topc(A_238))!=A_239 | ~m1_subset_1(u1_pre_topc(A_239), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_239)))) | ~v1_pre_topc(A_239) | ~l1_pre_topc(A_239) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_238), u1_pre_topc(A_238))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_238), u1_pre_topc(A_238))) | ~l1_pre_topc(A_238))), inference(superposition, [status(thm), theory('equality')], [c_1395, c_122])).
% 19.39/8.32  tff(c_5984, plain, (![A_240, A_241]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240)))=u1_pre_topc(A_241) | g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))!=A_241 | ~v1_pre_topc(A_241) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))) | ~l1_pre_topc(A_240) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_14, c_5959])).
% 19.39/8.32  tff(c_6016, plain, (![A_240]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_240), u1_pre_topc(A_240))) | ~l1_pre_topc(A_240) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_107, c_5984])).
% 19.39/8.32  tff(c_6038, plain, (![A_242]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_242), u1_pre_topc(A_242))) | ~l1_pre_topc(A_242))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_6016])).
% 19.39/8.32  tff(c_6110, plain, (![A_246]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_246), u1_pre_topc(A_246)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_246), u1_pre_topc(A_246))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_246), u1_pre_topc(A_246))) | ~l1_pre_topc(A_246))), inference(resolution, [status(thm)], [c_63, c_6038])).
% 19.39/8.32  tff(c_6151, plain, (![A_247]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_247), u1_pre_topc(A_247)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_247), u1_pre_topc(A_247))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_247))), inference(resolution, [status(thm)], [c_69, c_6110])).
% 19.39/8.32  tff(c_480, plain, (![A_91]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_423, c_69])).
% 19.39/8.32  tff(c_6739, plain, (![A_250]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(A_250))) | ~l1_pre_topc(A_250) | g1_pre_topc(u1_struct_0(A_250), u1_pre_topc(A_250))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_250))), inference(superposition, [status(thm), theory('equality')], [c_6151, c_480])).
% 19.39/8.32  tff(c_6802, plain, (![A_254]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_254), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(A_254), u1_pre_topc(A_254))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_254))), inference(resolution, [status(thm)], [c_69, c_6739])).
% 19.39/8.32  tff(c_6828, plain, (![A_1]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | k1_pre_topc('#skF_1', '#skF_3')!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6802])).
% 19.39/8.32  tff(c_483, plain, (![A_91]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_423, c_63])).
% 19.39/8.32  tff(c_6876, plain, (![A_256]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(A_256))) | ~l1_pre_topc(A_256) | g1_pre_topc(u1_struct_0(A_256), u1_pre_topc(A_256))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_256))), inference(superposition, [status(thm), theory('equality')], [c_6151, c_483])).
% 19.39/8.32  tff(c_6879, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_6828, c_6876])).
% 19.39/8.32  tff(c_6910, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_107, c_6879])).
% 19.39/8.32  tff(c_7010, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_6910])).
% 19.39/8.32  tff(c_7047, plain, (~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7010])).
% 19.39/8.32  tff(c_7053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_107, c_7047])).
% 19.39/8.32  tff(c_7055, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_6910])).
% 19.39/8.32  tff(c_454, plain, (![A_91, C_23]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_91, C_23)), u1_pre_topc(k1_pre_topc(A_91, C_23)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91)), C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~l1_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_423, c_24])).
% 19.39/8.32  tff(c_7298, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7055, c_454])).
% 19.39/8.32  tff(c_7570, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_95, c_95, c_7298])).
% 19.39/8.32  tff(c_176, plain, (![A_24]: (v2_compts_1('#skF_3', A_24) | ~v1_compts_1(k1_pre_topc(A_24, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_173, c_30])).
% 19.39/8.32  tff(c_466, plain, (![A_91]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91)), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_423, c_176])).
% 19.39/8.32  tff(c_7703, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7570, c_466])).
% 19.39/8.32  tff(c_7772, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_195, c_7703])).
% 19.39/8.32  tff(c_7773, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_134, c_7772])).
% 19.39/8.32  tff(c_7795, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_7773])).
% 19.39/8.32  tff(c_7801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_7795])).
% 19.39/8.32  tff(c_7803, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_172])).
% 19.39/8.32  tff(c_7802, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_172])).
% 19.39/8.32  tff(c_7825, plain, (![A_270, B_271]: (u1_struct_0(g1_pre_topc(A_270, B_271))=A_270 | ~m1_subset_1(B_271, k1_zfmisc_1(k1_zfmisc_1(A_270))) | ~v1_pre_topc(g1_pre_topc(A_270, B_271)) | ~l1_pre_topc(g1_pre_topc(A_270, B_271)))), inference(reflexivity, [status(thm), theory('equality')], [c_129])).
% 19.39/8.32  tff(c_7931, plain, (![A_280]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_280), u1_pre_topc(A_280)))=u1_struct_0(A_280) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_280), u1_pre_topc(A_280))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_280), u1_pre_topc(A_280))) | ~l1_pre_topc(A_280))), inference(resolution, [status(thm)], [c_14, c_7825])).
% 19.39/8.32  tff(c_7942, plain, (![A_281]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_281), u1_pre_topc(A_281)))=u1_struct_0(A_281) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_281), u1_pre_topc(A_281))) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_63, c_7931])).
% 19.39/8.32  tff(c_7953, plain, (![A_282]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282)))=u1_struct_0(A_282) | ~l1_pre_topc(A_282))), inference(resolution, [status(thm)], [c_69, c_7942])).
% 19.39/8.32  tff(c_9123, plain, (![A_321]: (g1_pre_topc(u1_struct_0(A_321), u1_pre_topc(g1_pre_topc(u1_struct_0(A_321), u1_pre_topc(A_321))))=g1_pre_topc(u1_struct_0(A_321), u1_pre_topc(A_321)) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_321), u1_pre_topc(A_321))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_321), u1_pre_topc(A_321))) | ~l1_pre_topc(A_321))), inference(superposition, [status(thm), theory('equality')], [c_7953, c_2])).
% 19.39/8.32  tff(c_13542, plain, (![A_430, A_431]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_430), u1_pre_topc(A_430)))=u1_pre_topc(A_431) | g1_pre_topc(u1_struct_0(A_430), u1_pre_topc(A_430))!=A_431 | ~m1_subset_1(u1_pre_topc(A_431), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_431)))) | ~v1_pre_topc(A_431) | ~l1_pre_topc(A_431) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_430), u1_pre_topc(A_430))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_430), u1_pre_topc(A_430))) | ~l1_pre_topc(A_430))), inference(superposition, [status(thm), theory('equality')], [c_9123, c_122])).
% 19.39/8.32  tff(c_13567, plain, (![A_432, A_433]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432)))=u1_pre_topc(A_433) | g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))!=A_433 | ~v1_pre_topc(A_433) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))) | ~l1_pre_topc(A_432) | ~l1_pre_topc(A_433))), inference(resolution, [status(thm)], [c_14, c_13542])).
% 19.39/8.32  tff(c_13599, plain, (![A_432]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))) | ~l1_pre_topc(A_432) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_107, c_13567])).
% 19.39/8.32  tff(c_13621, plain, (![A_434]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_434), u1_pre_topc(A_434)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_434), u1_pre_topc(A_434))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_434), u1_pre_topc(A_434))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_434), u1_pre_topc(A_434))) | ~l1_pre_topc(A_434))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_13599])).
% 19.39/8.32  tff(c_13693, plain, (![A_438]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_438), u1_pre_topc(A_438)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_438), u1_pre_topc(A_438))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_438), u1_pre_topc(A_438))) | ~l1_pre_topc(A_438))), inference(resolution, [status(thm)], [c_63, c_13621])).
% 19.39/8.32  tff(c_13734, plain, (![A_439]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_439), u1_pre_topc(A_439)))=u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | g1_pre_topc(u1_struct_0(A_439), u1_pre_topc(A_439))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_439))), inference(resolution, [status(thm)], [c_69, c_13693])).
% 19.39/8.32  tff(c_8010, plain, (![A_282]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~l1_pre_topc(A_282))), inference(superposition, [status(thm), theory('equality')], [c_7953, c_69])).
% 19.39/8.32  tff(c_14324, plain, (![A_442]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_442), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_442), u1_pre_topc(A_442))) | ~l1_pre_topc(A_442) | g1_pre_topc(u1_struct_0(A_442), u1_pre_topc(A_442))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_442))), inference(superposition, [status(thm), theory('equality')], [c_13734, c_8010])).
% 19.39/8.32  tff(c_14387, plain, (![A_446]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_446), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(A_446), u1_pre_topc(A_446))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_446))), inference(resolution, [status(thm)], [c_69, c_14324])).
% 19.39/8.32  tff(c_14413, plain, (![A_1]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | k1_pre_topc('#skF_1', '#skF_3')!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14387])).
% 19.39/8.32  tff(c_8013, plain, (![A_282]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~l1_pre_topc(A_282))), inference(superposition, [status(thm), theory('equality')], [c_7953, c_63])).
% 19.39/8.32  tff(c_14461, plain, (![A_448]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))) | ~l1_pre_topc(A_448) | g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))!=k1_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc(A_448))), inference(superposition, [status(thm), theory('equality')], [c_13734, c_8013])).
% 19.39/8.32  tff(c_14464, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_14413, c_14461])).
% 19.39/8.32  tff(c_14495, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_107, c_14464])).
% 19.39/8.32  tff(c_14595, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_14495])).
% 19.39/8.32  tff(c_14632, plain, (~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14595])).
% 19.39/8.32  tff(c_14638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_107, c_14632])).
% 19.39/8.32  tff(c_14640, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_14495])).
% 19.39/8.32  tff(c_7975, plain, (![A_282, C_23]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_282, C_23)), u1_pre_topc(k1_pre_topc(A_282, C_23)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282)), C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~l1_pre_topc(A_282))), inference(superposition, [status(thm), theory('equality')], [c_7953, c_24])).
% 19.39/8.32  tff(c_14885, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14640, c_7975])).
% 19.39/8.32  tff(c_15159, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_95, c_95, c_14885])).
% 19.39/8.32  tff(c_7990, plain, (![B_26, A_282]: (v2_compts_1(B_26, g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282)), B_26)) | k1_xboole_0=B_26 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~l1_pre_topc(A_282))), inference(superposition, [status(thm), theory('equality')], [c_7953, c_26])).
% 19.39/8.32  tff(c_15257, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15159, c_7990])).
% 19.39/8.32  tff(c_15329, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_3' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_7802, c_15257])).
% 19.39/8.32  tff(c_15330, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_7803, c_134, c_15329])).
% 19.39/8.32  tff(c_15423, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15330])).
% 19.39/8.32  tff(c_15429, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_15423])).
% 19.39/8.32  tff(c_15435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_15429])).
% 19.39/8.32  tff(c_15436, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_15330])).
% 19.39/8.32  tff(c_15445, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_15436])).
% 19.39/8.32  tff(c_15452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_15445])).
% 19.39/8.32  tff(c_15454, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 19.39/8.32  tff(c_15549, plain, (![A_478, B_479]: (u1_struct_0(g1_pre_topc(A_478, B_479))=A_478 | ~m1_subset_1(B_479, k1_zfmisc_1(k1_zfmisc_1(A_478))) | ~v1_pre_topc(g1_pre_topc(A_478, B_479)) | ~l1_pre_topc(g1_pre_topc(A_478, B_479)))), inference(reflexivity, [status(thm), theory('equality')], [c_129])).
% 19.39/8.32  tff(c_15559, plain, (![A_482]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_482), u1_pre_topc(A_482)))=u1_struct_0(A_482) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_482), u1_pre_topc(A_482))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_482), u1_pre_topc(A_482))) | ~l1_pre_topc(A_482))), inference(resolution, [status(thm)], [c_14, c_15549])).
% 19.39/8.32  tff(c_15570, plain, (![A_485]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_485), u1_pre_topc(A_485)))=u1_struct_0(A_485) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_485), u1_pre_topc(A_485))) | ~l1_pre_topc(A_485))), inference(resolution, [status(thm)], [c_63, c_15559])).
% 19.39/8.32  tff(c_15578, plain, (![A_486]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_486), u1_pre_topc(A_486)))=u1_struct_0(A_486) | ~l1_pre_topc(A_486))), inference(resolution, [status(thm)], [c_69, c_15570])).
% 19.39/8.32  tff(c_15453, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_44])).
% 19.39/8.32  tff(c_15461, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_15453])).
% 19.39/8.32  tff(c_15603, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15578, c_15461])).
% 19.39/8.32  tff(c_15636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_15603])).
% 19.39/8.32  tff(c_15638, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_15453])).
% 19.39/8.32  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_15714, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_15454, c_15638, c_42])).
% 19.39/8.32  tff(c_17080, plain, (![A_557, C_558]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_557, C_558)), u1_pre_topc(k1_pre_topc(A_557, C_558)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_557), u1_pre_topc(A_557)), C_558) | ~m1_subset_1(C_558, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_557), u1_pre_topc(A_557))))) | ~m1_subset_1(C_558, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.39/8.32  tff(c_17082, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15714, c_17080])).
% 19.39/8.32  tff(c_17089, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17082])).
% 19.39/8.32  tff(c_17340, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_17089])).
% 19.39/8.32  tff(c_15656, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15638, c_10])).
% 19.39/8.32  tff(c_15659, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15656])).
% 19.39/8.32  tff(c_15665, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_15659])).
% 19.39/8.32  tff(c_15671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_15665])).
% 19.39/8.32  tff(c_15673, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_15656])).
% 19.39/8.32  tff(c_17330, plain, (![A_573, B_574]: (u1_struct_0(g1_pre_topc(A_573, B_574))=A_573 | ~m1_subset_1(B_574, k1_zfmisc_1(k1_zfmisc_1(A_573))) | ~v1_pre_topc(g1_pre_topc(A_573, B_574)) | ~l1_pre_topc(g1_pre_topc(A_573, B_574)))), inference(reflexivity, [status(thm), theory('equality')], [c_129])).
% 19.39/8.32  tff(c_17423, plain, (![A_581]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_581), u1_pre_topc(A_581)))=u1_struct_0(A_581) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_581), u1_pre_topc(A_581))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_581), u1_pre_topc(A_581))) | ~l1_pre_topc(A_581))), inference(resolution, [status(thm)], [c_14, c_17330])).
% 19.39/8.32  tff(c_17439, plain, (![A_582]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_582), u1_pre_topc(A_582)))=u1_struct_0(A_582) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_582), u1_pre_topc(A_582))) | ~l1_pre_topc(A_582))), inference(resolution, [status(thm)], [c_63, c_17423])).
% 19.39/8.32  tff(c_17448, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_15673, c_17439])).
% 19.39/8.32  tff(c_17459, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17448])).
% 19.39/8.32  tff(c_17461, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17459, c_15714])).
% 19.39/8.32  tff(c_17464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17340, c_17461])).
% 19.39/8.32  tff(c_17466, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_17089])).
% 19.39/8.32  tff(c_17472, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17466, c_26])).
% 19.39/8.32  tff(c_17483, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_17472])).
% 19.39/8.32  tff(c_17484, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_96, c_17483])).
% 19.39/8.32  tff(c_17503, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_17484])).
% 19.39/8.32  tff(c_17474, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17466, c_8])).
% 19.39/8.32  tff(c_17487, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17474])).
% 19.39/8.32  tff(c_17499, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17487, c_12])).
% 19.39/8.32  tff(c_17502, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17499])).
% 19.39/8.32  tff(c_17477, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17466, c_10])).
% 19.39/8.32  tff(c_17490, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17477])).
% 19.39/8.32  tff(c_17465, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_17089])).
% 19.39/8.32  tff(c_17534, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17465, c_2])).
% 19.39/8.32  tff(c_17555, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17502, c_17490, c_17534])).
% 19.39/8.32  tff(c_15637, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_15453])).
% 19.39/8.32  tff(c_15763, plain, (![A_495, B_496]: (v1_compts_1(k1_pre_topc(A_495, B_496)) | ~v2_compts_1(B_496, A_495) | k1_xboole_0=B_496 | ~v2_pre_topc(A_495) | ~m1_subset_1(B_496, k1_zfmisc_1(u1_struct_0(A_495))) | ~l1_pre_topc(A_495))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_15766, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15714, c_15763])).
% 19.39/8.32  tff(c_15775, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15673, c_15637, c_15766])).
% 19.39/8.32  tff(c_17157, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15775])).
% 19.39/8.32  tff(c_17160, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_17157])).
% 19.39/8.32  tff(c_17167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_17160])).
% 19.39/8.32  tff(c_17168, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_15775])).
% 19.39/8.32  tff(c_17175, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_17168])).
% 19.39/8.32  tff(c_17564, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_17555, c_17175])).
% 19.39/8.32  tff(c_17569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17503, c_17564])).
% 19.39/8.32  tff(c_17571, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_17484])).
% 19.39/8.32  tff(c_17570, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17484])).
% 19.39/8.32  tff(c_17581, plain, (![A_583]: (v2_compts_1('#skF_2', A_583) | ~v1_compts_1(k1_pre_topc(A_583, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_583))) | ~l1_pre_topc(A_583))), inference(demodulation, [status(thm), theory('equality')], [c_17570, c_17570, c_17570, c_30])).
% 19.39/8.32  tff(c_17584, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17466, c_17581])).
% 19.39/8.32  tff(c_17590, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17571, c_17584])).
% 19.39/8.32  tff(c_17592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_17590])).
% 19.39/8.32  tff(c_17594, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_17168])).
% 19.39/8.32  tff(c_17593, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17168])).
% 19.39/8.32  tff(c_17665, plain, (![A_585]: (v1_compts_1(k1_pre_topc(A_585, '#skF_2')) | ~v2_compts_1('#skF_2', A_585) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_585))) | ~l1_pre_topc(A_585))), inference(demodulation, [status(thm), theory('equality')], [c_17593, c_17593, c_17593, c_32])).
% 19.39/8.32  tff(c_17668, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_15714, c_17665])).
% 19.39/8.32  tff(c_17671, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15673, c_15637, c_17668])).
% 19.39/8.32  tff(c_17673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17594, c_17671])).
% 19.39/8.32  tff(c_17675, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 19.39/8.32  tff(c_40, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_33523, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_33336, c_17675, c_40])).
% 19.39/8.32  tff(c_33524, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_33523])).
% 19.39/8.32  tff(c_33543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33521, c_33524])).
% 19.39/8.32  tff(c_33544, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_33523])).
% 19.39/8.32  tff(c_33560, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_33521, c_10])).
% 19.39/8.32  tff(c_33564, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_33560])).
% 19.39/8.32  tff(c_33570, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_33564])).
% 19.39/8.32  tff(c_33576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_33570])).
% 19.39/8.32  tff(c_33578, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_33560])).
% 19.39/8.32  tff(c_34023, plain, (![A_1079, B_1080]: (u1_pre_topc(g1_pre_topc(A_1079, B_1080))=B_1080 | ~m1_subset_1(B_1080, k1_zfmisc_1(k1_zfmisc_1(A_1079))) | ~v1_pre_topc(g1_pre_topc(A_1079, B_1080)) | ~l1_pre_topc(g1_pre_topc(A_1079, B_1080)))), inference(reflexivity, [status(thm), theory('equality')], [c_17711])).
% 19.39/8.32  tff(c_34114, plain, (![A_1087]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1087), u1_pre_topc(A_1087)))=u1_pre_topc(A_1087) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1087), u1_pre_topc(A_1087))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1087), u1_pre_topc(A_1087))) | ~l1_pre_topc(A_1087))), inference(resolution, [status(thm)], [c_14, c_34023])).
% 19.39/8.32  tff(c_34130, plain, (![A_1088]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1088), u1_pre_topc(A_1088)))=u1_pre_topc(A_1088) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1088), u1_pre_topc(A_1088))) | ~l1_pre_topc(A_1088))), inference(resolution, [status(thm)], [c_63, c_34114])).
% 19.39/8.32  tff(c_34139, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33578, c_34130])).
% 19.39/8.32  tff(c_34150, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34139])).
% 19.39/8.32  tff(c_34185, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34150, c_14])).
% 19.39/8.32  tff(c_34212, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_33578, c_34185])).
% 19.39/8.32  tff(c_34506, plain, (![C_1094, D_1095]: (u1_struct_0(g1_pre_topc(C_1094, D_1095))=C_1094 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_1094, D_1095)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1094, D_1095))))) | ~v1_pre_topc(g1_pre_topc(C_1094, D_1095)) | ~l1_pre_topc(g1_pre_topc(C_1094, D_1095)))), inference(reflexivity, [status(thm), theory('equality')], [c_17704])).
% 19.39/8.32  tff(c_34515, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34150, c_34506])).
% 19.39/8.32  tff(c_34540, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_33578, c_34212, c_34515])).
% 19.39/8.32  tff(c_34574, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_34540])).
% 19.39/8.32  tff(c_34580, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_63, c_34574])).
% 19.39/8.32  tff(c_34586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_34580])).
% 19.39/8.32  tff(c_34587, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_34540])).
% 19.39/8.32  tff(c_33580, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_33336, c_33521, c_42])).
% 19.39/8.32  tff(c_34626, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34587, c_33580])).
% 19.39/8.32  tff(c_34636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33544, c_34626])).
% 19.39/8.32  tff(c_34638, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 19.39/8.32  tff(c_34645, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34638, c_46])).
% 19.39/8.32  tff(c_34646, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34645])).
% 19.39/8.32  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.32  tff(c_34656, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_34638, c_48])).
% 19.39/8.32  tff(c_34816, plain, (![A_1128, C_1129]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_1128, C_1129)), u1_pre_topc(k1_pre_topc(A_1128, C_1129)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_1128), u1_pre_topc(A_1128)), C_1129) | ~m1_subset_1(C_1129, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1128), u1_pre_topc(A_1128))))) | ~m1_subset_1(C_1129, k1_zfmisc_1(u1_struct_0(A_1128))) | ~l1_pre_topc(A_1128))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.39/8.32  tff(c_34818, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34656, c_34816])).
% 19.39/8.32  tff(c_34823, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34818])).
% 19.39/8.32  tff(c_34824, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_34823])).
% 19.39/8.32  tff(c_34666, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_34656, c_10])).
% 19.39/8.32  tff(c_34680, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_34666])).
% 19.39/8.32  tff(c_34686, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_34680])).
% 19.39/8.32  tff(c_34692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_34686])).
% 19.39/8.32  tff(c_34694, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_34666])).
% 19.39/8.32  tff(c_34651, plain, (![C_1098, A_1099, D_1100, B_1101]: (C_1098=A_1099 | g1_pre_topc(C_1098, D_1100)!=g1_pre_topc(A_1099, B_1101) | ~m1_subset_1(B_1101, k1_zfmisc_1(k1_zfmisc_1(A_1099))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.32  tff(c_34653, plain, (![A_1, A_1099, B_1101]: (u1_struct_0(A_1)=A_1099 | g1_pre_topc(A_1099, B_1101)!=A_1 | ~m1_subset_1(B_1101, k1_zfmisc_1(k1_zfmisc_1(A_1099))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_34651])).
% 19.39/8.32  tff(c_34761, plain, (![A_1126, B_1127]: (u1_struct_0(g1_pre_topc(A_1126, B_1127))=A_1126 | ~m1_subset_1(B_1127, k1_zfmisc_1(k1_zfmisc_1(A_1126))) | ~v1_pre_topc(g1_pre_topc(A_1126, B_1127)) | ~l1_pre_topc(g1_pre_topc(A_1126, B_1127)))), inference(reflexivity, [status(thm), theory('equality')], [c_34653])).
% 19.39/8.32  tff(c_34825, plain, (![A_1130]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1130), u1_pre_topc(A_1130)))=u1_struct_0(A_1130) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1130), u1_pre_topc(A_1130))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1130), u1_pre_topc(A_1130))) | ~l1_pre_topc(A_1130))), inference(resolution, [status(thm)], [c_14, c_34761])).
% 19.39/8.32  tff(c_34841, plain, (![A_1132]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132)))=u1_struct_0(A_1132) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))) | ~l1_pre_topc(A_1132))), inference(resolution, [status(thm)], [c_63, c_34825])).
% 19.39/8.32  tff(c_34844, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34694, c_34841])).
% 19.39/8.32  tff(c_34853, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34844])).
% 19.39/8.32  tff(c_34855, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34853, c_34656])).
% 19.39/8.32  tff(c_34857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34824, c_34855])).
% 19.39/8.32  tff(c_34859, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_34823])).
% 19.39/8.32  tff(c_34862, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34859, c_26])).
% 19.39/8.32  tff(c_34873, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_34862])).
% 19.39/8.32  tff(c_34874, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34646, c_34873])).
% 19.39/8.32  tff(c_34934, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_34874])).
% 19.39/8.32  tff(c_34867, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34859, c_8])).
% 19.39/8.32  tff(c_34880, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34867])).
% 19.39/8.32  tff(c_34886, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34880, c_12])).
% 19.39/8.32  tff(c_34889, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34886])).
% 19.39/8.32  tff(c_34870, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34859, c_10])).
% 19.39/8.32  tff(c_34883, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34870])).
% 19.39/8.32  tff(c_34858, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(splitRight, [status(thm)], [c_34823])).
% 19.39/8.32  tff(c_34914, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34858, c_2])).
% 19.39/8.32  tff(c_34928, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34883, c_34914])).
% 19.39/8.32  tff(c_34939, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34889, c_34928])).
% 19.39/8.32  tff(c_34637, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 19.39/8.32  tff(c_34695, plain, (![A_1108, B_1109]: (v1_compts_1(k1_pre_topc(A_1108, B_1109)) | ~v2_compts_1(B_1109, A_1108) | k1_xboole_0=B_1109 | ~v2_pre_topc(A_1108) | ~m1_subset_1(B_1109, k1_zfmisc_1(u1_struct_0(A_1108))) | ~l1_pre_topc(A_1108))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.32  tff(c_34698, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_34656, c_34695])).
% 19.39/8.32  tff(c_34701, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34637, c_34698])).
% 19.39/8.32  tff(c_34791, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34694, c_34701])).
% 19.39/8.32  tff(c_34792, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_34791])).
% 19.39/8.32  tff(c_34795, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_34792])).
% 19.39/8.32  tff(c_34802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_34795])).
% 19.39/8.32  tff(c_34803, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_34791])).
% 19.39/8.32  tff(c_34810, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_34803])).
% 19.39/8.32  tff(c_34941, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34939, c_34810])).
% 19.39/8.32  tff(c_34946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34934, c_34941])).
% 19.39/8.32  tff(c_34948, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_34874])).
% 19.39/8.32  tff(c_34947, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34874])).
% 19.39/8.32  tff(c_35104, plain, (![A_1135]: (v2_compts_1('#skF_2', A_1135) | ~v1_compts_1(k1_pre_topc(A_1135, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1135))) | ~l1_pre_topc(A_1135))), inference(demodulation, [status(thm), theory('equality')], [c_34947, c_34947, c_34947, c_30])).
% 19.39/8.32  tff(c_35107, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34859, c_35104])).
% 19.39/8.32  tff(c_35113, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34948, c_35107])).
% 19.39/8.32  tff(c_35115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34646, c_35113])).
% 19.39/8.32  tff(c_35117, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_34803])).
% 19.39/8.32  tff(c_35116, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34803])).
% 19.39/8.32  tff(c_35131, plain, (![A_1136]: (v1_compts_1(k1_pre_topc(A_1136, '#skF_2')) | ~v2_compts_1('#skF_2', A_1136) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1136))) | ~l1_pre_topc(A_1136))), inference(demodulation, [status(thm), theory('equality')], [c_35116, c_35116, c_35116, c_32])).
% 19.39/8.32  tff(c_35134, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_34656, c_35131])).
% 19.39/8.32  tff(c_35137, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34694, c_34637, c_35134])).
% 19.39/8.32  tff(c_35139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35117, c_35137])).
% 19.39/8.32  tff(c_35140, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_34645])).
% 19.39/8.32  tff(c_35160, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_34638, c_48])).
% 19.39/8.32  tff(c_35170, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_35160, c_10])).
% 19.39/8.32  tff(c_35176, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_35170])).
% 19.39/8.33  tff(c_35182, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_35176])).
% 19.39/8.33  tff(c_35188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_35182])).
% 19.39/8.33  tff(c_35190, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_35170])).
% 19.39/8.33  tff(c_35155, plain, (![D_1141, B_1142, C_1143, A_1144]: (D_1141=B_1142 | g1_pre_topc(C_1143, D_1141)!=g1_pre_topc(A_1144, B_1142) | ~m1_subset_1(B_1142, k1_zfmisc_1(k1_zfmisc_1(A_1144))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.33  tff(c_35157, plain, (![A_1, B_1142, A_1144]: (u1_pre_topc(A_1)=B_1142 | g1_pre_topc(A_1144, B_1142)!=A_1 | ~m1_subset_1(B_1142, k1_zfmisc_1(k1_zfmisc_1(A_1144))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_35155])).
% 19.39/8.33  tff(c_35279, plain, (![A_1163, B_1164]: (u1_pre_topc(g1_pre_topc(A_1163, B_1164))=B_1164 | ~m1_subset_1(B_1164, k1_zfmisc_1(k1_zfmisc_1(A_1163))) | ~v1_pre_topc(g1_pre_topc(A_1163, B_1164)) | ~l1_pre_topc(g1_pre_topc(A_1163, B_1164)))), inference(reflexivity, [status(thm), theory('equality')], [c_35157])).
% 19.39/8.33  tff(c_35312, plain, (![A_1167]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1167), u1_pre_topc(A_1167)))=u1_pre_topc(A_1167) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1167), u1_pre_topc(A_1167))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1167), u1_pre_topc(A_1167))) | ~l1_pre_topc(A_1167))), inference(resolution, [status(thm)], [c_14, c_35279])).
% 19.39/8.33  tff(c_35328, plain, (![A_1170]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170)))=u1_pre_topc(A_1170) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170))) | ~l1_pre_topc(A_1170))), inference(resolution, [status(thm)], [c_63, c_35312])).
% 19.39/8.33  tff(c_35331, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35190, c_35328])).
% 19.39/8.33  tff(c_35340, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_35331])).
% 19.39/8.33  tff(c_35362, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35340, c_14])).
% 19.39/8.33  tff(c_35381, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_35190, c_35362])).
% 19.39/8.33  tff(c_35353, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35340, c_2])).
% 19.39/8.33  tff(c_35375, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35190, c_35353])).
% 19.39/8.33  tff(c_35584, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_35375])).
% 19.39/8.33  tff(c_35590, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_63, c_35584])).
% 19.39/8.33  tff(c_35596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_35590])).
% 19.39/8.33  tff(c_35597, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_35375])).
% 19.39/8.33  tff(c_22, plain, (![C_15, A_11, D_16, B_12]: (C_15=A_11 | g1_pre_topc(C_15, D_16)!=g1_pre_topc(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.33  tff(c_35635, plain, (![C_15, D_16]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=C_15 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_15, D_16) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))))), inference(superposition, [status(thm), theory('equality')], [c_35597, c_22])).
% 19.39/8.33  tff(c_35648, plain, (![C_15, D_16]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=C_15 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_15, D_16))), inference(demodulation, [status(thm), theory('equality')], [c_35381, c_35635])).
% 19.39/8.33  tff(c_35746, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_35648])).
% 19.39/8.33  tff(c_35764, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35746, c_35160])).
% 19.39/8.33  tff(c_35766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35140, c_35764])).
% 19.39/8.33  tff(c_35768, plain, (~v2_compts_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 19.39/8.33  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.33  tff(c_35794, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_35768, c_52])).
% 19.39/8.33  tff(c_35795, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_35794])).
% 19.39/8.33  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.39/8.33  tff(c_35799, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_35768, c_54])).
% 19.39/8.33  tff(c_35809, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_35799, c_10])).
% 19.39/8.33  tff(c_35834, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_35809])).
% 19.39/8.33  tff(c_35840, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_35834])).
% 19.39/8.33  tff(c_35846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_35840])).
% 19.39/8.33  tff(c_35848, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_35809])).
% 19.39/8.33  tff(c_35816, plain, (![C_1189, A_1190, D_1191, B_1192]: (C_1189=A_1190 | g1_pre_topc(C_1189, D_1191)!=g1_pre_topc(A_1190, B_1192) | ~m1_subset_1(B_1192, k1_zfmisc_1(k1_zfmisc_1(A_1190))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.33  tff(c_35818, plain, (![A_1, A_1190, B_1192]: (u1_struct_0(A_1)=A_1190 | g1_pre_topc(A_1190, B_1192)!=A_1 | ~m1_subset_1(B_1192, k1_zfmisc_1(k1_zfmisc_1(A_1190))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_35816])).
% 19.39/8.33  tff(c_35941, plain, (![A_1217, B_1218]: (u1_struct_0(g1_pre_topc(A_1217, B_1218))=A_1217 | ~m1_subset_1(B_1218, k1_zfmisc_1(k1_zfmisc_1(A_1217))) | ~v1_pre_topc(g1_pre_topc(A_1217, B_1218)) | ~l1_pre_topc(g1_pre_topc(A_1217, B_1218)))), inference(reflexivity, [status(thm), theory('equality')], [c_35818])).
% 19.39/8.33  tff(c_35969, plain, (![A_1219]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1219), u1_pre_topc(A_1219)))=u1_struct_0(A_1219) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1219), u1_pre_topc(A_1219))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1219), u1_pre_topc(A_1219))) | ~l1_pre_topc(A_1219))), inference(resolution, [status(thm)], [c_14, c_35941])).
% 19.39/8.33  tff(c_35977, plain, (![A_1220]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1220), u1_pre_topc(A_1220)))=u1_struct_0(A_1220) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1220), u1_pre_topc(A_1220))) | ~l1_pre_topc(A_1220))), inference(resolution, [status(thm)], [c_63, c_35969])).
% 19.39/8.33  tff(c_35980, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35848, c_35977])).
% 19.39/8.33  tff(c_35989, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_35980])).
% 19.39/8.33  tff(c_35999, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35989, c_35799])).
% 19.39/8.33  tff(c_36078, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35999, c_26])).
% 19.39/8.33  tff(c_36089, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_36078])).
% 19.39/8.33  tff(c_36090, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_35795, c_36089])).
% 19.39/8.33  tff(c_36100, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_36090])).
% 19.39/8.33  tff(c_36083, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35999, c_8])).
% 19.39/8.33  tff(c_36096, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36083])).
% 19.39/8.33  tff(c_36103, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36096, c_12])).
% 19.39/8.33  tff(c_36106, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36103])).
% 19.39/8.33  tff(c_36086, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35999, c_10])).
% 19.39/8.33  tff(c_36099, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36086])).
% 19.39/8.33  tff(c_35991, plain, (![A_1221, C_1222]: (g1_pre_topc(u1_struct_0(k1_pre_topc(A_1221, C_1222)), u1_pre_topc(k1_pre_topc(A_1221, C_1222)))=k1_pre_topc(g1_pre_topc(u1_struct_0(A_1221), u1_pre_topc(A_1221)), C_1222) | ~m1_subset_1(C_1222, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1221), u1_pre_topc(A_1221))))) | ~m1_subset_1(C_1222, k1_zfmisc_1(u1_struct_0(A_1221))) | ~l1_pre_topc(A_1221))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.39/8.33  tff(c_35993, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35799, c_35991])).
% 19.39/8.33  tff(c_35998, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_35993])).
% 19.39/8.33  tff(c_36185, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35999, c_35998])).
% 19.39/8.33  tff(c_36210, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36185, c_2])).
% 19.39/8.33  tff(c_36230, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')=k1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36106, c_36099, c_36210])).
% 19.39/8.33  tff(c_35767, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 19.39/8.33  tff(c_35854, plain, (![A_1199, B_1200]: (v1_compts_1(k1_pre_topc(A_1199, B_1200)) | ~v2_compts_1(B_1200, A_1199) | k1_xboole_0=B_1200 | ~v2_pre_topc(A_1199) | ~m1_subset_1(B_1200, k1_zfmisc_1(u1_struct_0(A_1199))) | ~l1_pre_topc(A_1199))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.39/8.33  tff(c_35857, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_35799, c_35854])).
% 19.39/8.33  tff(c_35860, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | k1_xboole_0='#skF_2' | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35848, c_35767, c_35857])).
% 19.39/8.33  tff(c_35866, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_35860])).
% 19.39/8.33  tff(c_35872, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_35866])).
% 19.39/8.33  tff(c_35878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_35872])).
% 19.39/8.33  tff(c_35879, plain, (k1_xboole_0='#skF_2' | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_35860])).
% 19.39/8.33  tff(c_35886, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_35879])).
% 19.39/8.33  tff(c_36253, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36230, c_35886])).
% 19.39/8.33  tff(c_36257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36100, c_36253])).
% 19.39/8.33  tff(c_36259, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_36090])).
% 19.39/8.33  tff(c_36258, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36090])).
% 19.39/8.33  tff(c_37087, plain, (![A_1244]: (v2_compts_1('#skF_2', A_1244) | ~v1_compts_1(k1_pre_topc(A_1244, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1244))) | ~l1_pre_topc(A_1244))), inference(demodulation, [status(thm), theory('equality')], [c_36258, c_36258, c_36258, c_30])).
% 19.39/8.33  tff(c_37093, plain, (v2_compts_1('#skF_2', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_35999, c_37087])).
% 19.39/8.33  tff(c_37099, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36259, c_37093])).
% 19.39/8.33  tff(c_37101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35795, c_37099])).
% 19.39/8.33  tff(c_37103, plain, (~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_35879])).
% 19.39/8.33  tff(c_37102, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_35879])).
% 19.39/8.33  tff(c_37124, plain, (![A_1246]: (v1_compts_1(k1_pre_topc(A_1246, '#skF_2')) | ~v2_compts_1('#skF_2', A_1246) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1246))) | ~l1_pre_topc(A_1246))), inference(demodulation, [status(thm), theory('equality')], [c_37102, c_37102, c_37102, c_32])).
% 19.39/8.33  tff(c_37127, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_35799, c_37124])).
% 19.39/8.33  tff(c_37130, plain, (v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35848, c_35767, c_37127])).
% 19.39/8.33  tff(c_37132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37103, c_37130])).
% 19.39/8.33  tff(c_37133, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_35794])).
% 19.39/8.33  tff(c_37136, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_35768, c_54])).
% 19.39/8.33  tff(c_37143, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_37136, c_10])).
% 19.39/8.33  tff(c_37175, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_37143])).
% 19.39/8.33  tff(c_37181, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_37175])).
% 19.39/8.33  tff(c_37187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_37181])).
% 19.39/8.33  tff(c_37189, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_37143])).
% 19.39/8.33  tff(c_37158, plain, (![C_1251, A_1252, D_1253, B_1254]: (C_1251=A_1252 | g1_pre_topc(C_1251, D_1253)!=g1_pre_topc(A_1252, B_1254) | ~m1_subset_1(B_1254, k1_zfmisc_1(k1_zfmisc_1(A_1252))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.39/8.33  tff(c_37160, plain, (![A_1, A_1252, B_1254]: (u1_struct_0(A_1)=A_1252 | g1_pre_topc(A_1252, B_1254)!=A_1 | ~m1_subset_1(B_1254, k1_zfmisc_1(k1_zfmisc_1(A_1252))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_37158])).
% 19.39/8.33  tff(c_37292, plain, (![A_1281, B_1282]: (u1_struct_0(g1_pre_topc(A_1281, B_1282))=A_1281 | ~m1_subset_1(B_1282, k1_zfmisc_1(k1_zfmisc_1(A_1281))) | ~v1_pre_topc(g1_pre_topc(A_1281, B_1282)) | ~l1_pre_topc(g1_pre_topc(A_1281, B_1282)))), inference(reflexivity, [status(thm), theory('equality')], [c_37160])).
% 19.39/8.33  tff(c_37328, plain, (![A_1285]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1285), u1_pre_topc(A_1285)))=u1_struct_0(A_1285) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1285), u1_pre_topc(A_1285))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1285), u1_pre_topc(A_1285))) | ~l1_pre_topc(A_1285))), inference(resolution, [status(thm)], [c_14, c_37292])).
% 19.39/8.33  tff(c_37336, plain, (![A_1286]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_1286), u1_pre_topc(A_1286)))=u1_struct_0(A_1286) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1286), u1_pre_topc(A_1286))) | ~l1_pre_topc(A_1286))), inference(resolution, [status(thm)], [c_63, c_37328])).
% 19.39/8.33  tff(c_37339, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_37189, c_37336])).
% 19.39/8.33  tff(c_37348, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_37339])).
% 19.39/8.33  tff(c_37350, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37348, c_37136])).
% 19.39/8.33  tff(c_37352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37133, c_37350])).
% 19.39/8.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.39/8.33  
% 19.39/8.33  Inference rules
% 19.39/8.33  ----------------------
% 19.39/8.33  #Ref     : 102
% 19.39/8.33  #Sup     : 11298
% 19.39/8.33  #Fact    : 0
% 19.39/8.33  #Define  : 0
% 19.39/8.33  #Split   : 61
% 19.39/8.33  #Chain   : 0
% 19.39/8.33  #Close   : 0
% 19.39/8.33  
% 19.39/8.33  Ordering : KBO
% 19.39/8.33  
% 19.39/8.33  Simplification rules
% 19.39/8.33  ----------------------
% 19.39/8.33  #Subsume      : 1466
% 19.39/8.33  #Demod        : 4884
% 19.39/8.33  #Tautology    : 1181
% 19.39/8.33  #SimpNegUnit  : 46
% 19.39/8.33  #BackRed      : 173
% 19.39/8.33  
% 19.39/8.33  #Partial instantiations: 0
% 19.39/8.33  #Strategies tried      : 1
% 19.39/8.33  
% 19.39/8.33  Timing (in seconds)
% 19.39/8.33  ----------------------
% 19.39/8.33  Preprocessing        : 0.33
% 19.39/8.33  Parsing              : 0.18
% 19.39/8.33  CNF conversion       : 0.02
% 19.39/8.33  Main loop            : 7.11
% 19.39/8.33  Inferencing          : 1.85
% 19.39/8.33  Reduction            : 2.04
% 19.39/8.33  Demodulation         : 1.48
% 19.39/8.33  BG Simplification    : 0.36
% 19.39/8.33  Subsumption          : 2.47
% 19.39/8.33  Abstraction          : 0.45
% 19.39/8.33  MUC search           : 0.00
% 19.39/8.33  Cooper               : 0.00
% 19.39/8.33  Total                : 7.59
% 19.39/8.33  Index Insertion      : 0.00
% 19.39/8.33  Index Deletion       : 0.00
% 19.39/8.33  Index Matching       : 0.00
% 19.39/8.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
