%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:11 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 271 expanded)
%              Number of leaves         :   23 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 ( 809 expanded)
%              Number of equality atoms :   22 ( 281 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tops_2(C,A) )
                     => v2_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_9)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(c_18,plain,(
    ~ v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_33,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_3] :
      ( m1_subset_1(u1_pre_topc(A_3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    ! [D_34,B_35,C_36,A_37] :
      ( D_34 = B_35
      | g1_pre_topc(C_36,D_34) != g1_pre_topc(A_37,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110,plain,(
    ! [B_42,A_43] :
      ( u1_pre_topc('#skF_2') = B_42
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_43,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_124,plain,(
    ! [A_3] :
      ( u1_pre_topc(A_3) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_110])).

tff(c_174,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_176,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_174])).

tff(c_207,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_4])).

tff(c_221,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_207])).

tff(c_49,plain,(
    ! [C_30,A_31,D_32,B_33] :
      ( C_30 = A_31
      | g1_pre_topc(C_30,D_32) != g1_pre_topc(A_31,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [C_30,D_32] :
      ( u1_struct_0('#skF_2') = C_30
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_30,D_32)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_49])).

tff(c_292,plain,(
    ! [C_30,D_32] :
      ( u1_struct_0('#skF_2') = C_30
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_30,D_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_176,c_53])).

tff(c_295,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_292])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( v2_tops_2(B_12,A_10)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_10),B_12),A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_310,plain,(
    ! [B_12] :
      ( v2_tops_2(B_12,'#skF_2')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_12),'#skF_2')
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_10])).

tff(c_432,plain,(
    ! [B_64] :
      ( v2_tops_2(B_64,'#skF_2')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_64),'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_295,c_310])).

tff(c_446,plain,
    ( v2_tops_2('#skF_4','#skF_2')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_432])).

tff(c_457,plain,(
    ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_446])).

tff(c_20,plain,(
    v2_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    v2_tops_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_135,plain,(
    ! [A_46,B_47] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_46),B_47),A_46)
      | ~ v2_tops_2(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_46))))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ v2_tops_2('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_135])).

tff(c_152,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_144])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(B_40,u1_pre_topc(A_41))
      | ~ v1_tops_2(B_40,A_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [A_41,B_2] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(A_41),B_2),u1_pre_topc(A_41))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_41),B_2),A_41)
      | ~ l1_pre_topc(A_41)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_63,plain,(
    ! [B_38,A_39] :
      ( v1_tops_2(B_38,A_39)
      | ~ r1_tarski(B_38,u1_pre_topc(A_39))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_371,plain,(
    ! [A_60,B_61] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_60),B_61),A_60)
      | ~ r1_tarski(k7_setfam_1(u1_struct_0(A_60),B_61),u1_pre_topc(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_377,plain,(
    ! [B_61] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),B_61),'#skF_2')
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_2'),B_61),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_371])).

tff(c_527,plain,(
    ! [B_70] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_70),'#skF_2')
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),B_70),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_30,c_295,c_295,c_377])).

tff(c_534,plain,(
    ! [B_2] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_2),'#skF_2')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_2),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_100,c_527])).

tff(c_539,plain,(
    ! [B_71] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_71),'#skF_2')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_71),'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_534])).

tff(c_553,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_539])).

tff(c_564,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_553])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  %$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.59/1.40  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.59/1.40  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.59/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.40  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.40  
% 2.59/1.42  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tops_2(C, A)) => v2_tops_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_waybel_9)).
% 2.59/1.42  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.59/1.42  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.59/1.42  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tops_2)).
% 2.59/1.42  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.59/1.42  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 2.59/1.42  tff(c_18, plain, (~v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_22, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_33, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28])).
% 2.59/1.42  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_4, plain, (![A_3]: (m1_subset_1(u1_pre_topc(A_3), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3)))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.42  tff(c_24, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_58, plain, (![D_34, B_35, C_36, A_37]: (D_34=B_35 | g1_pre_topc(C_36, D_34)!=g1_pre_topc(A_37, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.42  tff(c_110, plain, (![B_42, A_43]: (u1_pre_topc('#skF_2')=B_42 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_43, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_58])).
% 2.59/1.42  tff(c_124, plain, (![A_3]: (u1_pre_topc(A_3)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_3))), inference(resolution, [status(thm)], [c_4, c_110])).
% 2.59/1.42  tff(c_174, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_124])).
% 2.59/1.42  tff(c_176, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_174])).
% 2.59/1.42  tff(c_207, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_4])).
% 2.59/1.42  tff(c_221, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_207])).
% 2.59/1.42  tff(c_49, plain, (![C_30, A_31, D_32, B_33]: (C_30=A_31 | g1_pre_topc(C_30, D_32)!=g1_pre_topc(A_31, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.42  tff(c_53, plain, (![C_30, D_32]: (u1_struct_0('#skF_2')=C_30 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_30, D_32) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_49])).
% 2.59/1.42  tff(c_292, plain, (![C_30, D_32]: (u1_struct_0('#skF_2')=C_30 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_30, D_32))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_176, c_53])).
% 2.59/1.42  tff(c_295, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_292])).
% 2.59/1.42  tff(c_10, plain, (![B_12, A_10]: (v2_tops_2(B_12, A_10) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_10), B_12), A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.42  tff(c_310, plain, (![B_12]: (v2_tops_2(B_12, '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_12), '#skF_2') | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_10])).
% 2.59/1.42  tff(c_432, plain, (![B_64]: (v2_tops_2(B_64, '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_64), '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_295, c_310])).
% 2.59/1.42  tff(c_446, plain, (v2_tops_2('#skF_4', '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_33, c_432])).
% 2.59/1.42  tff(c_457, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18, c_446])).
% 2.59/1.42  tff(c_20, plain, (v2_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_34, plain, (v2_tops_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 2.59/1.42  tff(c_135, plain, (![A_46, B_47]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_46), B_47), A_46) | ~v2_tops_2(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_46)))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.42  tff(c_144, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~v2_tops_2('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33, c_135])).
% 2.59/1.42  tff(c_152, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_144])).
% 2.59/1.42  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.42  tff(c_86, plain, (![B_40, A_41]: (r1_tarski(B_40, u1_pre_topc(A_41)) | ~v1_tops_2(B_40, A_41) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.42  tff(c_100, plain, (![A_41, B_2]: (r1_tarski(k7_setfam_1(u1_struct_0(A_41), B_2), u1_pre_topc(A_41)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_41), B_2), A_41) | ~l1_pre_topc(A_41) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))))), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.59/1.42  tff(c_63, plain, (![B_38, A_39]: (v1_tops_2(B_38, A_39) | ~r1_tarski(B_38, u1_pre_topc(A_39)) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.42  tff(c_371, plain, (![A_60, B_61]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_60), B_61), A_60) | ~r1_tarski(k7_setfam_1(u1_struct_0(A_60), B_61), u1_pre_topc(A_60)) | ~l1_pre_topc(A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))))), inference(resolution, [status(thm)], [c_2, c_63])).
% 2.59/1.42  tff(c_377, plain, (![B_61]: (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), B_61), '#skF_2') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_2'), B_61), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_2') | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_176, c_371])).
% 2.59/1.42  tff(c_527, plain, (![B_70]: (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_70), '#skF_2') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), B_70), u1_pre_topc('#skF_1')) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_30, c_295, c_295, c_377])).
% 2.59/1.42  tff(c_534, plain, (![B_2]: (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_2), '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_2), '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_100, c_527])).
% 2.59/1.42  tff(c_539, plain, (![B_71]: (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_71), '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_71), '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_534])).
% 2.59/1.42  tff(c_553, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_33, c_539])).
% 2.59/1.42  tff(c_564, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_553])).
% 2.59/1.42  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_564])).
% 2.59/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.42  
% 2.59/1.42  Inference rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Ref     : 6
% 2.59/1.42  #Sup     : 96
% 2.59/1.42  #Fact    : 0
% 2.59/1.42  #Define  : 0
% 2.59/1.42  #Split   : 7
% 2.59/1.42  #Chain   : 0
% 2.59/1.42  #Close   : 0
% 2.59/1.42  
% 2.59/1.42  Ordering : KBO
% 2.59/1.42  
% 2.59/1.42  Simplification rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Subsume      : 36
% 2.59/1.42  #Demod        : 101
% 2.59/1.42  #Tautology    : 25
% 2.59/1.42  #SimpNegUnit  : 24
% 2.59/1.42  #BackRed      : 8
% 2.59/1.42  
% 2.59/1.42  #Partial instantiations: 0
% 2.59/1.42  #Strategies tried      : 1
% 2.59/1.42  
% 2.59/1.42  Timing (in seconds)
% 2.59/1.42  ----------------------
% 2.59/1.42  Preprocessing        : 0.30
% 2.59/1.42  Parsing              : 0.16
% 2.59/1.42  CNF conversion       : 0.02
% 2.59/1.42  Main loop            : 0.36
% 2.59/1.42  Inferencing          : 0.13
% 2.59/1.42  Reduction            : 0.11
% 2.59/1.42  Demodulation         : 0.08
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.06
% 2.59/1.42  Abstraction          : 0.02
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.69
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
