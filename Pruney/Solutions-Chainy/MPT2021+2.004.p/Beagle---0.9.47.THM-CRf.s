%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:11 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 234 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 701 expanded)
%              Number of equality atoms :   26 ( 192 expanded)
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

tff(f_84,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_20,plain,(
    ~ v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_35,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    v2_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v2_tops_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( k7_setfam_1(A_30,k7_setfam_1(A_30,B_31)) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35,c_46])).

tff(c_262,plain,(
    ! [B_56,A_57] :
      ( v1_tops_2(B_56,A_57)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(A_57),B_56),A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57))))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_268,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ v2_tops_2('#skF_4','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_262])).

tff(c_272,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_268])).

tff(c_565,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_568,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_565])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_568])).

tff(c_573,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_574,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_18,plain,(
    ! [B_17,A_15] :
      ( r1_tarski(B_17,u1_pre_topc(A_15))
      | ~ v1_tops_2(B_17,A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_591,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_574,c_18])).

tff(c_606,plain,(
    r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_573,c_591])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_5] :
      ( m1_subset_1(u1_pre_topc(A_5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_5))))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_101,plain,(
    ! [C_39,A_40,D_41,B_42] :
      ( C_39 = A_40
      | g1_pre_topc(C_39,D_41) != g1_pre_topc(A_40,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,(
    ! [A_45,B_46] :
      ( u1_struct_0('#skF_2') = A_45
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_101])).

tff(c_143,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_214,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_143])).

tff(c_216,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_214])).

tff(c_248,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_6])).

tff(c_260,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_248])).

tff(c_229,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_26])).

tff(c_8,plain,(
    ! [D_11,B_7,C_10,A_6] :
      ( D_11 = B_7
      | g1_pre_topc(C_10,D_11) != g1_pre_topc(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_305,plain,(
    ! [D_11,C_10] :
      ( u1_pre_topc('#skF_2') = D_11
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_10,D_11)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_8])).

tff(c_311,plain,(
    ! [D_11,C_10] :
      ( u1_pre_topc('#skF_2') = D_11
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_10,D_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_305])).

tff(c_330,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_311])).

tff(c_16,plain,(
    ! [B_17,A_15] :
      ( v1_tops_2(B_17,A_15)
      | ~ r1_tarski(B_17,u1_pre_topc(A_15))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_236,plain,(
    ! [B_17] :
      ( v1_tops_2(B_17,'#skF_2')
      | ~ r1_tarski(B_17,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_16])).

tff(c_252,plain,(
    ! [B_17] :
      ( v1_tops_2(B_17,'#skF_2')
      | ~ r1_tarski(B_17,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_236])).

tff(c_489,plain,(
    ! [B_17] :
      ( v1_tops_2(B_17,'#skF_2')
      | ~ r1_tarski(B_17,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_252])).

tff(c_595,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2')
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_574,c_489])).

tff(c_611,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_595])).

tff(c_337,plain,(
    ! [A_60,B_61] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0(A_60),B_61),A_60)
      | ~ v1_tops_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_341,plain,(
    ! [B_61] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),B_61),'#skF_2')
      | ~ v1_tops_2(B_61,'#skF_2')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_337])).

tff(c_612,plain,(
    ! [B_71] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),B_71),'#skF_2')
      | ~ v1_tops_2(B_71,'#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_216,c_341])).

tff(c_615,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4')),'#skF_2')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_574,c_612])).

tff(c_632,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_55,c_615])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:22:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  %$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.69/1.39  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.69/1.39  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.69/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.69/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.39  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.69/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.39  
% 2.69/1.41  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tops_2(C, A)) => v2_tops_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_waybel_9)).
% 2.69/1.41  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.69/1.41  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.69/1.41  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> v2_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tops_2)).
% 2.69/1.41  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 2.69/1.41  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.69/1.41  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.69/1.41  tff(c_20, plain, (~v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_24, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_35, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.69/1.41  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.41  tff(c_22, plain, (v2_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_36, plain, (v2_tops_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 2.69/1.41  tff(c_46, plain, (![A_30, B_31]: (k7_setfam_1(A_30, k7_setfam_1(A_30, B_31))=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.41  tff(c_55, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_35, c_46])).
% 2.69/1.41  tff(c_262, plain, (![B_56, A_57]: (v1_tops_2(B_56, A_57) | ~v2_tops_2(k7_setfam_1(u1_struct_0(A_57), B_56), A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57)))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.41  tff(c_268, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~v2_tops_2('#skF_4', '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_55, c_262])).
% 2.69/1.41  tff(c_272, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_268])).
% 2.69/1.41  tff(c_565, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_272])).
% 2.69/1.41  tff(c_568, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_565])).
% 2.69/1.41  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_568])).
% 2.69/1.41  tff(c_573, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_272])).
% 2.69/1.41  tff(c_574, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_272])).
% 2.69/1.41  tff(c_18, plain, (![B_17, A_15]: (r1_tarski(B_17, u1_pre_topc(A_15)) | ~v1_tops_2(B_17, A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.41  tff(c_591, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), u1_pre_topc('#skF_1')) | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_574, c_18])).
% 2.69/1.41  tff(c_606, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_573, c_591])).
% 2.69/1.41  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_6, plain, (![A_5]: (m1_subset_1(u1_pre_topc(A_5), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_5)))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.41  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.41  tff(c_101, plain, (![C_39, A_40, D_41, B_42]: (C_39=A_40 | g1_pre_topc(C_39, D_41)!=g1_pre_topc(A_40, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.41  tff(c_129, plain, (![A_45, B_46]: (u1_struct_0('#skF_2')=A_45 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_101])).
% 2.69/1.41  tff(c_143, plain, (![A_5]: (u1_struct_0(A_5)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.69/1.41  tff(c_214, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_143])).
% 2.69/1.41  tff(c_216, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_214])).
% 2.69/1.41  tff(c_248, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_216, c_6])).
% 2.69/1.41  tff(c_260, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_248])).
% 2.69/1.41  tff(c_229, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_26])).
% 2.69/1.41  tff(c_8, plain, (![D_11, B_7, C_10, A_6]: (D_11=B_7 | g1_pre_topc(C_10, D_11)!=g1_pre_topc(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.41  tff(c_305, plain, (![D_11, C_10]: (u1_pre_topc('#skF_2')=D_11 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_10, D_11) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_229, c_8])).
% 2.69/1.41  tff(c_311, plain, (![D_11, C_10]: (u1_pre_topc('#skF_2')=D_11 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_10, D_11))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_305])).
% 2.69/1.41  tff(c_330, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_311])).
% 2.69/1.41  tff(c_16, plain, (![B_17, A_15]: (v1_tops_2(B_17, A_15) | ~r1_tarski(B_17, u1_pre_topc(A_15)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.41  tff(c_236, plain, (![B_17]: (v1_tops_2(B_17, '#skF_2') | ~r1_tarski(B_17, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_16])).
% 2.69/1.41  tff(c_252, plain, (![B_17]: (v1_tops_2(B_17, '#skF_2') | ~r1_tarski(B_17, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_236])).
% 2.69/1.41  tff(c_489, plain, (![B_17]: (v1_tops_2(B_17, '#skF_2') | ~r1_tarski(B_17, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_252])).
% 2.69/1.41  tff(c_595, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_574, c_489])).
% 2.69/1.41  tff(c_611, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_595])).
% 2.69/1.41  tff(c_337, plain, (![A_60, B_61]: (v2_tops_2(k7_setfam_1(u1_struct_0(A_60), B_61), A_60) | ~v1_tops_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.41  tff(c_341, plain, (![B_61]: (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), B_61), '#skF_2') | ~v1_tops_2(B_61, '#skF_2') | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_337])).
% 2.69/1.41  tff(c_612, plain, (![B_71]: (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), B_71), '#skF_2') | ~v1_tops_2(B_71, '#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_216, c_341])).
% 2.69/1.41  tff(c_615, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4')), '#skF_2') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_574, c_612])).
% 2.69/1.41  tff(c_632, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_55, c_615])).
% 2.69/1.41  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_632])).
% 2.69/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  Inference rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Ref     : 6
% 2.69/1.41  #Sup     : 123
% 2.69/1.41  #Fact    : 0
% 2.69/1.41  #Define  : 0
% 2.69/1.41  #Split   : 6
% 2.69/1.41  #Chain   : 0
% 2.69/1.41  #Close   : 0
% 2.69/1.41  
% 2.69/1.41  Ordering : KBO
% 2.69/1.41  
% 2.69/1.41  Simplification rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Subsume      : 30
% 2.69/1.41  #Demod        : 126
% 2.69/1.41  #Tautology    : 51
% 2.69/1.41  #SimpNegUnit  : 18
% 2.69/1.41  #BackRed      : 12
% 2.69/1.41  
% 2.69/1.41  #Partial instantiations: 0
% 2.69/1.41  #Strategies tried      : 1
% 2.69/1.41  
% 2.69/1.41  Timing (in seconds)
% 2.69/1.41  ----------------------
% 2.69/1.41  Preprocessing        : 0.31
% 2.69/1.41  Parsing              : 0.17
% 2.69/1.41  CNF conversion       : 0.02
% 2.69/1.41  Main loop            : 0.33
% 2.69/1.41  Inferencing          : 0.11
% 2.69/1.41  Reduction            : 0.11
% 2.69/1.41  Demodulation         : 0.08
% 2.69/1.41  BG Simplification    : 0.02
% 2.69/1.41  Subsumption          : 0.06
% 2.69/1.41  Abstraction          : 0.02
% 2.69/1.41  MUC search           : 0.00
% 2.69/1.41  Cooper               : 0.00
% 2.69/1.41  Total                : 0.67
% 2.69/1.41  Index Insertion      : 0.00
% 2.69/1.41  Index Deletion       : 0.00
% 2.69/1.41  Index Matching       : 0.00
% 2.69/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
