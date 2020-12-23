%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:02 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  247 (1082 expanded)
%              Number of leaves         :   23 ( 328 expanded)
%              Depth                    :   14
%              Number of atoms          :  516 (3151 expanded)
%              Number of equality atoms :  103 ( 292 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_tops_2(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
          <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,
    ( v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_8,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_18,B_19] :
      ( l1_pre_topc(g1_pre_topc(A_18,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_4] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( v1_pre_topc(g1_pre_topc(A_16,B_17))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_4] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_42])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [C_27,A_28,D_29,B_30] :
      ( C_27 = A_28
      | g1_pre_topc(C_27,D_29) != g1_pre_topc(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [A_1,C_27,D_29] :
      ( u1_struct_0(A_1) = C_27
      | g1_pre_topc(C_27,D_29) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_3300,plain,(
    ! [C_130,D_131] :
      ( u1_struct_0(g1_pre_topc(C_130,D_131)) = C_130
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_130,D_131)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_130,D_131)))))
      | ~ v1_pre_topc(g1_pre_topc(C_130,D_131))
      | ~ l1_pre_topc(g1_pre_topc(C_130,D_131)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_97])).

tff(c_3324,plain,(
    ! [C_132,D_133] :
      ( u1_struct_0(g1_pre_topc(C_132,D_133)) = C_132
      | ~ v1_pre_topc(g1_pre_topc(C_132,D_133))
      | ~ l1_pre_topc(g1_pre_topc(C_132,D_133)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3300])).

tff(c_3342,plain,(
    ! [A_134] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_134),u1_pre_topc(A_134))) = u1_struct_0(A_134)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_134),u1_pre_topc(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_46,c_3324])).

tff(c_3363,plain,(
    ! [A_135] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135))) = u1_struct_0(A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_51,c_3342])).

tff(c_479,plain,(
    ! [C_66,D_67] :
      ( u1_struct_0(g1_pre_topc(C_66,D_67)) = C_66
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_66,D_67)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_66,D_67)))))
      | ~ v1_pre_topc(g1_pre_topc(C_66,D_67))
      | ~ l1_pre_topc(g1_pre_topc(C_66,D_67)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_97])).

tff(c_500,plain,(
    ! [C_68,D_69] :
      ( u1_struct_0(g1_pre_topc(C_68,D_69)) = C_68
      | ~ v1_pre_topc(g1_pre_topc(C_68,D_69))
      | ~ l1_pre_topc(g1_pre_topc(C_68,D_69)) ) ),
    inference(resolution,[status(thm)],[c_8,c_479])).

tff(c_533,plain,(
    ! [A_71] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_71),u1_pre_topc(A_71))) = u1_struct_0(A_71)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_71),u1_pre_topc(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_46,c_500])).

tff(c_551,plain,(
    ! [A_72] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_72),u1_pre_topc(A_72))) = u1_struct_0(A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_51,c_533])).

tff(c_821,plain,(
    ! [A_79] :
      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(A_79),u1_pre_topc(A_79))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_79),u1_pre_topc(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_8])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_6])).

tff(c_84,plain,(
    ! [D_23,B_24,C_25,A_26] :
      ( D_23 = B_24
      | g1_pre_topc(C_25,D_23) != g1_pre_topc(A_26,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    ! [A_1,B_24,A_26] :
      ( u1_pre_topc(A_1) = B_24
      | g1_pre_topc(A_26,B_24) != A_1
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_341,plain,(
    ! [A_56,B_57] :
      ( u1_pre_topc(g1_pre_topc(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56)))
      | ~ v1_pre_topc(g1_pre_topc(A_56,B_57))
      | ~ l1_pre_topc(g1_pre_topc(A_56,B_57)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_86])).

tff(c_347,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_341])).

tff(c_356,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_347])).

tff(c_95,plain,(
    ! [A_1,A_28,B_30] :
      ( u1_struct_0(A_1) = A_28
      | g1_pre_topc(A_28,B_30) != A_1
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_28)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_171,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0(g1_pre_topc(A_49,B_50)) = A_49
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49)))
      | ~ v1_pre_topc(g1_pre_topc(A_49,B_50))
      | ~ l1_pre_topc(g1_pre_topc(A_49,B_50)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_95])).

tff(c_174,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_171])).

tff(c_180,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_174])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( v1_tops_2(B_13,A_11)
      | ~ r1_tarski(B_13,u1_pre_topc(A_11))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_185,plain,(
    ! [B_13] :
      ( v1_tops_2(B_13,g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ r1_tarski(B_13,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_14])).

tff(c_204,plain,(
    ! [B_13] :
      ( v1_tops_2(B_13,g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ r1_tarski(B_13,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3')))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_185])).

tff(c_518,plain,(
    ! [B_13] :
      ( v1_tops_2(B_13,g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ r1_tarski(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_204])).

tff(c_825,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_821,c_518])).

tff(c_868,plain,
    ( v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),g1_pre_topc(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_825])).

tff(c_1401,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_1407,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_1401])).

tff(c_1413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1407])).

tff(c_1415,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_40,plain,
    ( v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v1_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    v1_tops_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_100,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,u1_pre_topc(A_32))
      | ~ v1_tops_2(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_32))))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,
    ( r1_tarski('#skF_3',u1_pre_topc('#skF_1'))
    | ~ v1_tops_2('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_100])).

tff(c_109,plain,(
    r1_tarski('#skF_3',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_69,c_103])).

tff(c_88,plain,(
    ! [A_1,D_23,C_25] :
      ( u1_pre_topc(A_1) = D_23
      | g1_pre_topc(C_25,D_23) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_419,plain,(
    ! [C_60,D_61] :
      ( u1_pre_topc(g1_pre_topc(C_60,D_61)) = D_61
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_60,D_61)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_60,D_61)))))
      | ~ v1_pre_topc(g1_pre_topc(C_60,D_61))
      | ~ l1_pre_topc(g1_pre_topc(C_60,D_61)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_447,plain,(
    ! [C_63,D_64] :
      ( u1_pre_topc(g1_pre_topc(C_63,D_64)) = D_64
      | ~ v1_pre_topc(g1_pre_topc(C_63,D_64))
      | ~ l1_pre_topc(g1_pre_topc(C_63,D_64)) ) ),
    inference(resolution,[status(thm)],[c_8,c_419])).

tff(c_598,plain,(
    ! [A_73] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_73),u1_pre_topc(A_73))) = u1_pre_topc(A_73)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_73),u1_pre_topc(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_46,c_447])).

tff(c_618,plain,(
    ! [A_4] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4))) = u1_pre_topc(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_51,c_598])).

tff(c_2752,plain,(
    ! [B_109,A_110] :
      ( v1_tops_2(B_109,g1_pre_topc(u1_struct_0(A_110),u1_pre_topc(A_110)))
      | ~ r1_tarski(B_109,u1_pre_topc(g1_pre_topc(u1_struct_0(A_110),u1_pre_topc(A_110))))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_110))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_110),u1_pre_topc(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_14])).

tff(c_2815,plain,(
    ! [B_111,A_112] :
      ( v1_tops_2(B_111,g1_pre_topc(u1_struct_0(A_112),u1_pre_topc(A_112)))
      | ~ r1_tarski(B_111,u1_pre_topc(A_112))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_112),u1_pre_topc(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_2752])).

tff(c_28,plain,
    ( v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_tops_2('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_156,plain,(
    ~ v1_tops_2('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2841,plain,
    ( ~ r1_tarski('#skF_3',u1_pre_topc('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2815,c_156])).

tff(c_2878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1415,c_71,c_109,c_2841])).

tff(c_2879,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2896,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(splitLeft,[status(thm)],[c_2879])).

tff(c_3387,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3363,c_2896])).

tff(c_3427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_71,c_3387])).

tff(c_3429,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(splitRight,[status(thm)],[c_2879])).

tff(c_24,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_tops_2('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2881,plain,(
    ~ v1_tops_2('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2880,plain,(
    v1_tops_2('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2881,c_2880])).

tff(c_2888,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_3478,plain,
    ( ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3429,c_2888])).

tff(c_3479,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_3478])).

tff(c_3428,plain,(
    v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2879])).

tff(c_26,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_tops_2('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3431,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_26])).

tff(c_3432,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(splitLeft,[status(thm)],[c_3431])).

tff(c_3444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3432,c_3429])).

tff(c_3445,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(splitRight,[status(thm)],[c_3431])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(B_13,u1_pre_topc(A_11))
      | ~ v1_tops_2(B_13,A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3496,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3445,c_16])).

tff(c_3510,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3428,c_3496])).

tff(c_3526,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3510])).

tff(c_3532,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_3526])).

tff(c_3538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3532])).

tff(c_3540,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3510])).

tff(c_3952,plain,(
    ! [C_143,D_144] :
      ( u1_struct_0(g1_pre_topc(C_143,D_144)) = C_143
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_143,D_144)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_143,D_144)))))
      | ~ v1_pre_topc(g1_pre_topc(C_143,D_144))
      | ~ l1_pre_topc(g1_pre_topc(C_143,D_144)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_97])).

tff(c_4048,plain,(
    ! [C_147,D_148] :
      ( u1_struct_0(g1_pre_topc(C_147,D_148)) = C_147
      | ~ v1_pre_topc(g1_pre_topc(C_147,D_148))
      | ~ l1_pre_topc(g1_pre_topc(C_147,D_148)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3952])).

tff(c_4580,plain,(
    ! [A_161] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_161),u1_pre_topc(A_161))) = u1_struct_0(A_161)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_161),u1_pre_topc(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_46,c_4048])).

tff(c_4610,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3540,c_4580])).

tff(c_4635,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4610])).

tff(c_4653,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4635,c_3445])).

tff(c_4663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3479,c_4653])).

tff(c_4664,plain,(
    ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3478])).

tff(c_4665,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_3478])).

tff(c_4668,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4665,c_14])).

tff(c_4680,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4668])).

tff(c_4681,plain,(
    ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_4664,c_4680])).

tff(c_4703,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3445,c_16])).

tff(c_4717,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3428,c_4703])).

tff(c_4732,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4717])).

tff(c_4738,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_4732])).

tff(c_4744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4738])).

tff(c_4746,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4717])).

tff(c_5043,plain,(
    ! [C_169,D_170] :
      ( u1_pre_topc(g1_pre_topc(C_169,D_170)) = D_170
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_169,D_170)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_169,D_170)))))
      | ~ v1_pre_topc(g1_pre_topc(C_169,D_170))
      | ~ l1_pre_topc(g1_pre_topc(C_169,D_170)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_5282,plain,(
    ! [C_175,D_176] :
      ( u1_pre_topc(g1_pre_topc(C_175,D_176)) = D_176
      | ~ v1_pre_topc(g1_pre_topc(C_175,D_176))
      | ~ l1_pre_topc(g1_pre_topc(C_175,D_176)) ) ),
    inference(resolution,[status(thm)],[c_8,c_5043])).

tff(c_5839,plain,(
    ! [A_183] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183))) = u1_pre_topc(A_183)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(resolution,[status(thm)],[c_46,c_5282])).

tff(c_5863,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4746,c_5839])).

tff(c_5884,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5863])).

tff(c_4745,plain,(
    r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_4717])).

tff(c_5895,plain,(
    r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5884,c_4745])).

tff(c_5901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4681,c_5895])).

tff(c_5903,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_tops_2('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5934,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_5903,c_30])).

tff(c_5935,plain,(
    ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5934])).

tff(c_5902,plain,(
    v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5942,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_5903,c_32])).

tff(c_5945,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_5942,c_16])).

tff(c_5960,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_5945])).

tff(c_5982,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5960])).

tff(c_5988,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_5982])).

tff(c_5994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5988])).

tff(c_5996,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_5960])).

tff(c_5915,plain,(
    ! [C_184,A_185,D_186,B_187] :
      ( C_184 = A_185
      | g1_pre_topc(C_184,D_186) != g1_pre_topc(A_185,B_187)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k1_zfmisc_1(A_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5919,plain,(
    ! [A_1,C_184,D_186] :
      ( u1_struct_0(A_1) = C_184
      | g1_pre_topc(C_184,D_186) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5915])).

tff(c_6285,plain,(
    ! [C_214,D_215] :
      ( u1_struct_0(g1_pre_topc(C_214,D_215)) = C_214
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_214,D_215)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_214,D_215)))))
      | ~ v1_pre_topc(g1_pre_topc(C_214,D_215))
      | ~ l1_pre_topc(g1_pre_topc(C_214,D_215)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5919])).

tff(c_6306,plain,(
    ! [C_216,D_217] :
      ( u1_struct_0(g1_pre_topc(C_216,D_217)) = C_216
      | ~ v1_pre_topc(g1_pre_topc(C_216,D_217))
      | ~ l1_pre_topc(g1_pre_topc(C_216,D_217)) ) ),
    inference(resolution,[status(thm)],[c_8,c_6285])).

tff(c_6320,plain,(
    ! [A_218] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_218),u1_pre_topc(A_218))) = u1_struct_0(A_218)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_218),u1_pre_topc(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_46,c_6306])).

tff(c_6329,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_5996,c_6320])).

tff(c_6342,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6329])).

tff(c_6349,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_5942])).

tff(c_6402,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6349,c_14])).

tff(c_6415,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6402])).

tff(c_6416,plain,(
    ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_5935,c_6415])).

tff(c_5924,plain,(
    ! [D_188,B_189,C_190,A_191] :
      ( D_188 = B_189
      | g1_pre_topc(C_190,D_188) != g1_pre_topc(A_191,B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k1_zfmisc_1(A_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5928,plain,(
    ! [A_1,D_188,C_190] :
      ( u1_pre_topc(A_1) = D_188
      | g1_pre_topc(C_190,D_188) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5924])).

tff(c_6427,plain,(
    ! [C_219,D_220] :
      ( u1_pre_topc(g1_pre_topc(C_219,D_220)) = D_220
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_219,D_220)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_219,D_220)))))
      | ~ v1_pre_topc(g1_pre_topc(C_219,D_220))
      | ~ l1_pre_topc(g1_pre_topc(C_219,D_220)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5928])).

tff(c_6548,plain,(
    ! [C_221,D_222] :
      ( u1_pre_topc(g1_pre_topc(C_221,D_222)) = D_222
      | ~ v1_pre_topc(g1_pre_topc(C_221,D_222))
      | ~ l1_pre_topc(g1_pre_topc(C_221,D_222)) ) ),
    inference(resolution,[status(thm)],[c_8,c_6427])).

tff(c_6817,plain,(
    ! [A_226] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_226),u1_pre_topc(A_226))) = u1_pre_topc(A_226)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_226),u1_pre_topc(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(resolution,[status(thm)],[c_46,c_6548])).

tff(c_6835,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_5996,c_6817])).

tff(c_6852,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6835])).

tff(c_5995,plain,(
    r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_5960])).

tff(c_6861,plain,(
    r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6852,c_5995])).

tff(c_6866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6416,c_6861])).

tff(c_6867,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_5934])).

tff(c_6869,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_5903,c_32])).

tff(c_6899,plain,(
    ! [B_228,A_229] :
      ( r1_tarski(B_228,u1_pre_topc(A_229))
      | ~ v1_tops_2(B_228,A_229)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_229))))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6902,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6869,c_6899])).

tff(c_6908,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_6902])).

tff(c_6916,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6908])).

tff(c_6922,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_6916])).

tff(c_6928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6922])).

tff(c_6930,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6908])).

tff(c_7116,plain,(
    ! [C_247,D_248] :
      ( u1_struct_0(g1_pre_topc(C_247,D_248)) = C_247
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_247,D_248)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_247,D_248)))))
      | ~ v1_pre_topc(g1_pre_topc(C_247,D_248))
      | ~ l1_pre_topc(g1_pre_topc(C_247,D_248)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5919])).

tff(c_7137,plain,(
    ! [C_249,D_250] :
      ( u1_struct_0(g1_pre_topc(C_249,D_250)) = C_249
      | ~ v1_pre_topc(g1_pre_topc(C_249,D_250))
      | ~ l1_pre_topc(g1_pre_topc(C_249,D_250)) ) ),
    inference(resolution,[status(thm)],[c_8,c_7116])).

tff(c_7154,plain,(
    ! [A_251] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251))) = u1_struct_0(A_251)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_251),u1_pre_topc(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(resolution,[status(thm)],[c_46,c_7137])).

tff(c_7163,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6930,c_7154])).

tff(c_7176,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7163])).

tff(c_7183,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7176,c_6869])).

tff(c_7185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6867,c_7183])).

tff(c_7187,plain,(
    ~ v1_tops_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_tops_2('#skF_2','#skF_1')
    | v1_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7194,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_7187,c_36])).

tff(c_7195,plain,(
    ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7194])).

tff(c_7186,plain,(
    v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | v1_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7196,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_7187,c_38])).

tff(c_7239,plain,(
    ! [B_260,A_261] :
      ( r1_tarski(B_260,u1_pre_topc(A_261))
      | ~ v1_tops_2(B_260,A_261)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_261))))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7242,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7196,c_7239])).

tff(c_7248,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7186,c_7242])).

tff(c_7251,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7248])).

tff(c_7257,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_7251])).

tff(c_7263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7257])).

tff(c_7265,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7248])).

tff(c_7234,plain,(
    ! [C_256,A_257,D_258,B_259] :
      ( C_256 = A_257
      | g1_pre_topc(C_256,D_258) != g1_pre_topc(A_257,B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k1_zfmisc_1(A_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7236,plain,(
    ! [A_1,A_257,B_259] :
      ( u1_struct_0(A_1) = A_257
      | g1_pre_topc(A_257,B_259) != A_1
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k1_zfmisc_1(A_257)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7234])).

tff(c_7500,plain,(
    ! [A_280,B_281] :
      ( u1_struct_0(g1_pre_topc(A_280,B_281)) = A_280
      | ~ m1_subset_1(B_281,k1_zfmisc_1(k1_zfmisc_1(A_280)))
      | ~ v1_pre_topc(g1_pre_topc(A_280,B_281))
      | ~ l1_pre_topc(g1_pre_topc(A_280,B_281)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7236])).

tff(c_7570,plain,(
    ! [A_282] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282))) = u1_struct_0(A_282)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_282),u1_pre_topc(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_8,c_7500])).

tff(c_7588,plain,(
    ! [A_283] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_283),u1_pre_topc(A_283))) = u1_struct_0(A_283)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_283),u1_pre_topc(A_283)))
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_46,c_7570])).

tff(c_7597,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7265,c_7588])).

tff(c_7610,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7597])).

tff(c_7617,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7610,c_7196])).

tff(c_7686,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7617,c_14])).

tff(c_7704,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7686])).

tff(c_7705,plain,(
    ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_7195,c_7704])).

tff(c_7225,plain,(
    ! [D_252,B_253,C_254,A_255] :
      ( D_252 = B_253
      | g1_pre_topc(C_254,D_252) != g1_pre_topc(A_255,B_253)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k1_zfmisc_1(A_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7229,plain,(
    ! [A_1,D_252,C_254] :
      ( u1_pre_topc(A_1) = D_252
      | g1_pre_topc(C_254,D_252) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7225])).

tff(c_7770,plain,(
    ! [C_286,D_287] :
      ( u1_pre_topc(g1_pre_topc(C_286,D_287)) = D_287
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_286,D_287)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_286,D_287)))))
      | ~ v1_pre_topc(g1_pre_topc(C_286,D_287))
      | ~ l1_pre_topc(g1_pre_topc(C_286,D_287)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7229])).

tff(c_7938,plain,(
    ! [C_290,D_291] :
      ( u1_pre_topc(g1_pre_topc(C_290,D_291)) = D_291
      | ~ v1_pre_topc(g1_pre_topc(C_290,D_291))
      | ~ l1_pre_topc(g1_pre_topc(C_290,D_291)) ) ),
    inference(resolution,[status(thm)],[c_8,c_7770])).

tff(c_8143,plain,(
    ! [A_295] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_295),u1_pre_topc(A_295))) = u1_pre_topc(A_295)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_295),u1_pre_topc(A_295)))
      | ~ l1_pre_topc(A_295) ) ),
    inference(resolution,[status(thm)],[c_46,c_7938])).

tff(c_8161,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7265,c_8143])).

tff(c_8178,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8161])).

tff(c_7264,plain,(
    r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_7248])).

tff(c_8187,plain,(
    r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8178,c_7264])).

tff(c_8192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7705,c_8187])).

tff(c_8193,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_7194])).

tff(c_8204,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_7187,c_38])).

tff(c_8239,plain,(
    ! [B_304,A_305] :
      ( r1_tarski(B_304,u1_pre_topc(A_305))
      | ~ v1_tops_2(B_304,A_305)
      | ~ m1_subset_1(B_304,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305))))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8242,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_tops_2('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8204,c_8239])).

tff(c_8248,plain,
    ( r1_tarski('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7186,c_8242])).

tff(c_8251,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8248])).

tff(c_8259,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_8251])).

tff(c_8265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8259])).

tff(c_8267,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8248])).

tff(c_8234,plain,(
    ! [D_300,B_301,C_302,A_303] :
      ( D_300 = B_301
      | g1_pre_topc(C_302,D_300) != g1_pre_topc(A_303,B_301)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(k1_zfmisc_1(A_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8236,plain,(
    ! [A_1,B_301,A_303] :
      ( u1_pre_topc(A_1) = B_301
      | g1_pre_topc(A_303,B_301) != A_1
      | ~ m1_subset_1(B_301,k1_zfmisc_1(k1_zfmisc_1(A_303)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8234])).

tff(c_8334,plain,(
    ! [A_322,B_323] :
      ( u1_pre_topc(g1_pre_topc(A_322,B_323)) = B_323
      | ~ m1_subset_1(B_323,k1_zfmisc_1(k1_zfmisc_1(A_322)))
      | ~ v1_pre_topc(g1_pre_topc(A_322,B_323))
      | ~ l1_pre_topc(g1_pre_topc(A_322,B_323)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8236])).

tff(c_8607,plain,(
    ! [A_327] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_327),u1_pre_topc(A_327))) = u1_pre_topc(A_327)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_327),u1_pre_topc(A_327)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_327),u1_pre_topc(A_327)))
      | ~ l1_pre_topc(A_327) ) ),
    inference(resolution,[status(thm)],[c_8,c_8334])).

tff(c_8625,plain,(
    ! [A_328] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_328),u1_pre_topc(A_328))) = u1_pre_topc(A_328)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_328),u1_pre_topc(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(resolution,[status(thm)],[c_46,c_8607])).

tff(c_8634,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8267,c_8625])).

tff(c_8647,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8634])).

tff(c_8677,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8647,c_8])).

tff(c_8700,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8267,c_8677])).

tff(c_8199,plain,(
    ! [C_296,A_297,D_298,B_299] :
      ( C_296 = A_297
      | g1_pre_topc(C_296,D_298) != g1_pre_topc(A_297,B_299)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k1_zfmisc_1(A_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8203,plain,(
    ! [A_1,C_296,D_298] :
      ( u1_struct_0(A_1) = C_296
      | g1_pre_topc(C_296,D_298) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8199])).

tff(c_8959,plain,(
    ! [C_335,D_336] :
      ( u1_struct_0(g1_pre_topc(C_335,D_336)) = C_335
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_335,D_336)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_335,D_336)))))
      | ~ v1_pre_topc(g1_pre_topc(C_335,D_336))
      | ~ l1_pre_topc(g1_pre_topc(C_335,D_336)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8203])).

tff(c_8968,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8647,c_8959])).

tff(c_8987,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8267,c_8700,c_8968])).

tff(c_9030,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8987])).

tff(c_9036,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_9030])).

tff(c_9042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9036])).

tff(c_9043,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8987])).

tff(c_9081,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9043,c_8204])).

tff(c_9086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8193,c_9081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.78  
% 7.18/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.79  %$ v1_tops_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.18/2.79  
% 7.18/2.79  %Foreground sorts:
% 7.18/2.79  
% 7.18/2.79  
% 7.18/2.79  %Background operators:
% 7.18/2.79  
% 7.18/2.79  
% 7.18/2.79  %Foreground operators:
% 7.18/2.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.18/2.79  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.18/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.79  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.18/2.79  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 7.18/2.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.18/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.18/2.79  tff('#skF_2', type, '#skF_2': $i).
% 7.18/2.79  tff('#skF_3', type, '#skF_3': $i).
% 7.18/2.79  tff('#skF_1', type, '#skF_1': $i).
% 7.18/2.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.18/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.18/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.18/2.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.18/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.18/2.79  
% 7.66/2.82  tff(f_76, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_compts_1)).
% 7.66/2.82  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.66/2.82  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 7.66/2.82  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 7.66/2.82  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 7.66/2.82  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 7.66/2.82  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_34, plain, (v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_34])).
% 7.66/2.82  tff(c_8, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.66/2.82  tff(c_47, plain, (![A_18, B_19]: (l1_pre_topc(g1_pre_topc(A_18, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.66/2.82  tff(c_51, plain, (![A_4]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_47])).
% 7.66/2.82  tff(c_42, plain, (![A_16, B_17]: (v1_pre_topc(g1_pre_topc(A_16, B_17)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.66/2.82  tff(c_46, plain, (![A_4]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_42])).
% 7.66/2.82  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.66/2.82  tff(c_93, plain, (![C_27, A_28, D_29, B_30]: (C_27=A_28 | g1_pre_topc(C_27, D_29)!=g1_pre_topc(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_97, plain, (![A_1, C_27, D_29]: (u1_struct_0(A_1)=C_27 | g1_pre_topc(C_27, D_29)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_93])).
% 7.66/2.82  tff(c_3300, plain, (![C_130, D_131]: (u1_struct_0(g1_pre_topc(C_130, D_131))=C_130 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_130, D_131)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_130, D_131))))) | ~v1_pre_topc(g1_pre_topc(C_130, D_131)) | ~l1_pre_topc(g1_pre_topc(C_130, D_131)))), inference(reflexivity, [status(thm), theory('equality')], [c_97])).
% 7.66/2.82  tff(c_3324, plain, (![C_132, D_133]: (u1_struct_0(g1_pre_topc(C_132, D_133))=C_132 | ~v1_pre_topc(g1_pre_topc(C_132, D_133)) | ~l1_pre_topc(g1_pre_topc(C_132, D_133)))), inference(resolution, [status(thm)], [c_8, c_3300])).
% 7.66/2.82  tff(c_3342, plain, (![A_134]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_134), u1_pre_topc(A_134)))=u1_struct_0(A_134) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_134), u1_pre_topc(A_134))) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_46, c_3324])).
% 7.66/2.82  tff(c_3363, plain, (![A_135]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135)))=u1_struct_0(A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_51, c_3342])).
% 7.66/2.82  tff(c_479, plain, (![C_66, D_67]: (u1_struct_0(g1_pre_topc(C_66, D_67))=C_66 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_66, D_67)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_66, D_67))))) | ~v1_pre_topc(g1_pre_topc(C_66, D_67)) | ~l1_pre_topc(g1_pre_topc(C_66, D_67)))), inference(reflexivity, [status(thm), theory('equality')], [c_97])).
% 7.66/2.82  tff(c_500, plain, (![C_68, D_69]: (u1_struct_0(g1_pre_topc(C_68, D_69))=C_68 | ~v1_pre_topc(g1_pre_topc(C_68, D_69)) | ~l1_pre_topc(g1_pre_topc(C_68, D_69)))), inference(resolution, [status(thm)], [c_8, c_479])).
% 7.66/2.82  tff(c_533, plain, (![A_71]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_71), u1_pre_topc(A_71)))=u1_struct_0(A_71) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_71), u1_pre_topc(A_71))) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_46, c_500])).
% 7.66/2.82  tff(c_551, plain, (![A_72]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_72), u1_pre_topc(A_72)))=u1_struct_0(A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_51, c_533])).
% 7.66/2.82  tff(c_821, plain, (![A_79]: (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(A_79), u1_pre_topc(A_79))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_79), u1_pre_topc(A_79))) | ~l1_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_551, c_8])).
% 7.66/2.82  tff(c_4, plain, (![A_2, B_3]: (l1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.66/2.82  tff(c_78, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_4])).
% 7.66/2.82  tff(c_6, plain, (![A_2, B_3]: (v1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.66/2.82  tff(c_79, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_6])).
% 7.66/2.82  tff(c_84, plain, (![D_23, B_24, C_25, A_26]: (D_23=B_24 | g1_pre_topc(C_25, D_23)!=g1_pre_topc(A_26, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_86, plain, (![A_1, B_24, A_26]: (u1_pre_topc(A_1)=B_24 | g1_pre_topc(A_26, B_24)!=A_1 | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 7.66/2.82  tff(c_341, plain, (![A_56, B_57]: (u1_pre_topc(g1_pre_topc(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))) | ~v1_pre_topc(g1_pre_topc(A_56, B_57)) | ~l1_pre_topc(g1_pre_topc(A_56, B_57)))), inference(reflexivity, [status(thm), theory('equality')], [c_86])).
% 7.66/2.82  tff(c_347, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3' | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_341])).
% 7.66/2.82  tff(c_356, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79, c_347])).
% 7.66/2.82  tff(c_95, plain, (![A_1, A_28, B_30]: (u1_struct_0(A_1)=A_28 | g1_pre_topc(A_28, B_30)!=A_1 | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_28))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_93])).
% 7.66/2.82  tff(c_171, plain, (![A_49, B_50]: (u1_struct_0(g1_pre_topc(A_49, B_50))=A_49 | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))) | ~v1_pre_topc(g1_pre_topc(A_49, B_50)) | ~l1_pre_topc(g1_pre_topc(A_49, B_50)))), inference(reflexivity, [status(thm), theory('equality')], [c_95])).
% 7.66/2.82  tff(c_174, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_171])).
% 7.66/2.82  tff(c_180, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79, c_174])).
% 7.66/2.82  tff(c_14, plain, (![B_13, A_11]: (v1_tops_2(B_13, A_11) | ~r1_tarski(B_13, u1_pre_topc(A_11)) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.82  tff(c_185, plain, (![B_13]: (v1_tops_2(B_13, g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~r1_tarski(B_13, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_180, c_14])).
% 7.66/2.82  tff(c_204, plain, (![B_13]: (v1_tops_2(B_13, g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~r1_tarski(B_13, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3'))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_185])).
% 7.66/2.82  tff(c_518, plain, (![B_13]: (v1_tops_2(B_13, g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~r1_tarski(B_13, '#skF_3') | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_204])).
% 7.66/2.82  tff(c_825, plain, (v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_821, c_518])).
% 7.66/2.82  tff(c_868, plain, (v1_tops_2(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), g1_pre_topc(u1_struct_0('#skF_1'), '#skF_3')) | ~r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_825])).
% 7.66/2.82  tff(c_1401, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_868])).
% 7.66/2.82  tff(c_1407, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_1401])).
% 7.66/2.82  tff(c_1413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1407])).
% 7.66/2.82  tff(c_1415, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_868])).
% 7.66/2.82  tff(c_40, plain, (v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v1_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_69, plain, (v1_tops_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 7.66/2.82  tff(c_100, plain, (![B_31, A_32]: (r1_tarski(B_31, u1_pre_topc(A_32)) | ~v1_tops_2(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_32)))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.82  tff(c_103, plain, (r1_tarski('#skF_3', u1_pre_topc('#skF_1')) | ~v1_tops_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_71, c_100])).
% 7.66/2.82  tff(c_109, plain, (r1_tarski('#skF_3', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_69, c_103])).
% 7.66/2.82  tff(c_88, plain, (![A_1, D_23, C_25]: (u1_pre_topc(A_1)=D_23 | g1_pre_topc(C_25, D_23)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 7.66/2.82  tff(c_419, plain, (![C_60, D_61]: (u1_pre_topc(g1_pre_topc(C_60, D_61))=D_61 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_60, D_61)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_60, D_61))))) | ~v1_pre_topc(g1_pre_topc(C_60, D_61)) | ~l1_pre_topc(g1_pre_topc(C_60, D_61)))), inference(reflexivity, [status(thm), theory('equality')], [c_88])).
% 7.66/2.82  tff(c_447, plain, (![C_63, D_64]: (u1_pre_topc(g1_pre_topc(C_63, D_64))=D_64 | ~v1_pre_topc(g1_pre_topc(C_63, D_64)) | ~l1_pre_topc(g1_pre_topc(C_63, D_64)))), inference(resolution, [status(thm)], [c_8, c_419])).
% 7.66/2.82  tff(c_598, plain, (![A_73]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_73), u1_pre_topc(A_73)))=u1_pre_topc(A_73) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_73), u1_pre_topc(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_46, c_447])).
% 7.66/2.82  tff(c_618, plain, (![A_4]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4)))=u1_pre_topc(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_51, c_598])).
% 7.66/2.82  tff(c_2752, plain, (![B_109, A_110]: (v1_tops_2(B_109, g1_pre_topc(u1_struct_0(A_110), u1_pre_topc(A_110))) | ~r1_tarski(B_109, u1_pre_topc(g1_pre_topc(u1_struct_0(A_110), u1_pre_topc(A_110)))) | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_110)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_110), u1_pre_topc(A_110))) | ~l1_pre_topc(A_110))), inference(superposition, [status(thm), theory('equality')], [c_551, c_14])).
% 7.66/2.82  tff(c_2815, plain, (![B_111, A_112]: (v1_tops_2(B_111, g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))) | ~r1_tarski(B_111, u1_pre_topc(A_112)) | ~m1_subset_1(B_111, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))) | ~l1_pre_topc(A_112) | ~l1_pre_topc(A_112))), inference(superposition, [status(thm), theory('equality')], [c_618, c_2752])).
% 7.66/2.82  tff(c_28, plain, (v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_tops_2('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_156, plain, (~v1_tops_2('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_28])).
% 7.66/2.82  tff(c_2841, plain, (~r1_tarski('#skF_3', u1_pre_topc('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2815, c_156])).
% 7.66/2.82  tff(c_2878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1415, c_71, c_109, c_2841])).
% 7.66/2.82  tff(c_2879, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 7.66/2.82  tff(c_2896, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(splitLeft, [status(thm)], [c_2879])).
% 7.66/2.82  tff(c_3387, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3363, c_2896])).
% 7.66/2.82  tff(c_3427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_71, c_3387])).
% 7.66/2.82  tff(c_3429, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(splitRight, [status(thm)], [c_2879])).
% 7.66/2.82  tff(c_24, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_tops_2('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_2881, plain, (~v1_tops_2('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_24])).
% 7.66/2.82  tff(c_2880, plain, (v1_tops_2('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 7.66/2.82  tff(c_2887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2881, c_2880])).
% 7.66/2.82  tff(c_2888, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_24])).
% 7.66/2.82  tff(c_3478, plain, (~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_3429, c_2888])).
% 7.66/2.82  tff(c_3479, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_3478])).
% 7.66/2.82  tff(c_3428, plain, (v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2879])).
% 7.66/2.82  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_tops_2('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_3431, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_26])).
% 7.66/2.82  tff(c_3432, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(splitLeft, [status(thm)], [c_3431])).
% 7.66/2.82  tff(c_3444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3432, c_3429])).
% 7.66/2.82  tff(c_3445, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(splitRight, [status(thm)], [c_3431])).
% 7.66/2.82  tff(c_16, plain, (![B_13, A_11]: (r1_tarski(B_13, u1_pre_topc(A_11)) | ~v1_tops_2(B_13, A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.82  tff(c_3496, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_3445, c_16])).
% 7.66/2.82  tff(c_3510, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3428, c_3496])).
% 7.66/2.82  tff(c_3526, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3510])).
% 7.66/2.82  tff(c_3532, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_3526])).
% 7.66/2.82  tff(c_3538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_3532])).
% 7.66/2.82  tff(c_3540, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_3510])).
% 7.66/2.82  tff(c_3952, plain, (![C_143, D_144]: (u1_struct_0(g1_pre_topc(C_143, D_144))=C_143 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_143, D_144)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_143, D_144))))) | ~v1_pre_topc(g1_pre_topc(C_143, D_144)) | ~l1_pre_topc(g1_pre_topc(C_143, D_144)))), inference(reflexivity, [status(thm), theory('equality')], [c_97])).
% 7.66/2.82  tff(c_4048, plain, (![C_147, D_148]: (u1_struct_0(g1_pre_topc(C_147, D_148))=C_147 | ~v1_pre_topc(g1_pre_topc(C_147, D_148)) | ~l1_pre_topc(g1_pre_topc(C_147, D_148)))), inference(resolution, [status(thm)], [c_8, c_3952])).
% 7.66/2.82  tff(c_4580, plain, (![A_161]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_161), u1_pre_topc(A_161)))=u1_struct_0(A_161) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_161), u1_pre_topc(A_161))) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_46, c_4048])).
% 7.66/2.82  tff(c_4610, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3540, c_4580])).
% 7.66/2.82  tff(c_4635, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4610])).
% 7.66/2.82  tff(c_4653, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_4635, c_3445])).
% 7.66/2.82  tff(c_4663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3479, c_4653])).
% 7.66/2.82  tff(c_4664, plain, (~v1_tops_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_3478])).
% 7.66/2.82  tff(c_4665, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_3478])).
% 7.66/2.82  tff(c_4668, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4665, c_14])).
% 7.66/2.82  tff(c_4680, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4668])).
% 7.66/2.82  tff(c_4681, plain, (~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_4664, c_4680])).
% 7.66/2.82  tff(c_4703, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_3445, c_16])).
% 7.66/2.82  tff(c_4717, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3428, c_4703])).
% 7.66/2.82  tff(c_4732, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_4717])).
% 7.66/2.82  tff(c_4738, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_4732])).
% 7.66/2.82  tff(c_4744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_4738])).
% 7.66/2.82  tff(c_4746, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_4717])).
% 7.66/2.82  tff(c_5043, plain, (![C_169, D_170]: (u1_pre_topc(g1_pre_topc(C_169, D_170))=D_170 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_169, D_170)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_169, D_170))))) | ~v1_pre_topc(g1_pre_topc(C_169, D_170)) | ~l1_pre_topc(g1_pre_topc(C_169, D_170)))), inference(reflexivity, [status(thm), theory('equality')], [c_88])).
% 7.66/2.82  tff(c_5282, plain, (![C_175, D_176]: (u1_pre_topc(g1_pre_topc(C_175, D_176))=D_176 | ~v1_pre_topc(g1_pre_topc(C_175, D_176)) | ~l1_pre_topc(g1_pre_topc(C_175, D_176)))), inference(resolution, [status(thm)], [c_8, c_5043])).
% 7.66/2.82  tff(c_5839, plain, (![A_183]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183)))=u1_pre_topc(A_183) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183))) | ~l1_pre_topc(A_183))), inference(resolution, [status(thm)], [c_46, c_5282])).
% 7.66/2.82  tff(c_5863, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4746, c_5839])).
% 7.66/2.82  tff(c_5884, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5863])).
% 7.66/2.82  tff(c_4745, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_4717])).
% 7.66/2.82  tff(c_5895, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5884, c_4745])).
% 7.66/2.82  tff(c_5901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4681, c_5895])).
% 7.66/2.82  tff(c_5903, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_34])).
% 7.66/2.82  tff(c_30, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_5934, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_5903, c_30])).
% 7.66/2.82  tff(c_5935, plain, (~v1_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_5934])).
% 7.66/2.82  tff(c_5902, plain, (v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_34])).
% 7.66/2.82  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_5942, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(negUnitSimplification, [status(thm)], [c_5903, c_32])).
% 7.66/2.82  tff(c_5945, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_5942, c_16])).
% 7.66/2.82  tff(c_5960, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5902, c_5945])).
% 7.66/2.82  tff(c_5982, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_5960])).
% 7.66/2.82  tff(c_5988, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_5982])).
% 7.66/2.82  tff(c_5994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_5988])).
% 7.66/2.82  tff(c_5996, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_5960])).
% 7.66/2.82  tff(c_5915, plain, (![C_184, A_185, D_186, B_187]: (C_184=A_185 | g1_pre_topc(C_184, D_186)!=g1_pre_topc(A_185, B_187) | ~m1_subset_1(B_187, k1_zfmisc_1(k1_zfmisc_1(A_185))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_5919, plain, (![A_1, C_184, D_186]: (u1_struct_0(A_1)=C_184 | g1_pre_topc(C_184, D_186)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5915])).
% 7.66/2.82  tff(c_6285, plain, (![C_214, D_215]: (u1_struct_0(g1_pre_topc(C_214, D_215))=C_214 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_214, D_215)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_214, D_215))))) | ~v1_pre_topc(g1_pre_topc(C_214, D_215)) | ~l1_pre_topc(g1_pre_topc(C_214, D_215)))), inference(reflexivity, [status(thm), theory('equality')], [c_5919])).
% 7.66/2.82  tff(c_6306, plain, (![C_216, D_217]: (u1_struct_0(g1_pre_topc(C_216, D_217))=C_216 | ~v1_pre_topc(g1_pre_topc(C_216, D_217)) | ~l1_pre_topc(g1_pre_topc(C_216, D_217)))), inference(resolution, [status(thm)], [c_8, c_6285])).
% 7.66/2.82  tff(c_6320, plain, (![A_218]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_218), u1_pre_topc(A_218)))=u1_struct_0(A_218) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_218), u1_pre_topc(A_218))) | ~l1_pre_topc(A_218))), inference(resolution, [status(thm)], [c_46, c_6306])).
% 7.66/2.82  tff(c_6329, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_5996, c_6320])).
% 7.66/2.82  tff(c_6342, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6329])).
% 7.66/2.82  tff(c_6349, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_5942])).
% 7.66/2.82  tff(c_6402, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6349, c_14])).
% 7.66/2.82  tff(c_6415, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6402])).
% 7.66/2.82  tff(c_6416, plain, (~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_5935, c_6415])).
% 7.66/2.82  tff(c_5924, plain, (![D_188, B_189, C_190, A_191]: (D_188=B_189 | g1_pre_topc(C_190, D_188)!=g1_pre_topc(A_191, B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(k1_zfmisc_1(A_191))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_5928, plain, (![A_1, D_188, C_190]: (u1_pre_topc(A_1)=D_188 | g1_pre_topc(C_190, D_188)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5924])).
% 7.66/2.82  tff(c_6427, plain, (![C_219, D_220]: (u1_pre_topc(g1_pre_topc(C_219, D_220))=D_220 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_219, D_220)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_219, D_220))))) | ~v1_pre_topc(g1_pre_topc(C_219, D_220)) | ~l1_pre_topc(g1_pre_topc(C_219, D_220)))), inference(reflexivity, [status(thm), theory('equality')], [c_5928])).
% 7.66/2.82  tff(c_6548, plain, (![C_221, D_222]: (u1_pre_topc(g1_pre_topc(C_221, D_222))=D_222 | ~v1_pre_topc(g1_pre_topc(C_221, D_222)) | ~l1_pre_topc(g1_pre_topc(C_221, D_222)))), inference(resolution, [status(thm)], [c_8, c_6427])).
% 7.66/2.82  tff(c_6817, plain, (![A_226]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_226), u1_pre_topc(A_226)))=u1_pre_topc(A_226) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_226), u1_pre_topc(A_226))) | ~l1_pre_topc(A_226))), inference(resolution, [status(thm)], [c_46, c_6548])).
% 7.66/2.82  tff(c_6835, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_5996, c_6817])).
% 7.66/2.82  tff(c_6852, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6835])).
% 7.66/2.82  tff(c_5995, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_5960])).
% 7.66/2.82  tff(c_6861, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6852, c_5995])).
% 7.66/2.82  tff(c_6866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6416, c_6861])).
% 7.66/2.82  tff(c_6867, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_5934])).
% 7.66/2.82  tff(c_6869, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(negUnitSimplification, [status(thm)], [c_5903, c_32])).
% 7.66/2.82  tff(c_6899, plain, (![B_228, A_229]: (r1_tarski(B_228, u1_pre_topc(A_229)) | ~v1_tops_2(B_228, A_229) | ~m1_subset_1(B_228, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_229)))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.82  tff(c_6902, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_6869, c_6899])).
% 7.66/2.82  tff(c_6908, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5902, c_6902])).
% 7.66/2.82  tff(c_6916, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_6908])).
% 7.66/2.82  tff(c_6922, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_6916])).
% 7.66/2.82  tff(c_6928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_6922])).
% 7.66/2.82  tff(c_6930, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_6908])).
% 7.66/2.82  tff(c_7116, plain, (![C_247, D_248]: (u1_struct_0(g1_pre_topc(C_247, D_248))=C_247 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_247, D_248)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_247, D_248))))) | ~v1_pre_topc(g1_pre_topc(C_247, D_248)) | ~l1_pre_topc(g1_pre_topc(C_247, D_248)))), inference(reflexivity, [status(thm), theory('equality')], [c_5919])).
% 7.66/2.82  tff(c_7137, plain, (![C_249, D_250]: (u1_struct_0(g1_pre_topc(C_249, D_250))=C_249 | ~v1_pre_topc(g1_pre_topc(C_249, D_250)) | ~l1_pre_topc(g1_pre_topc(C_249, D_250)))), inference(resolution, [status(thm)], [c_8, c_7116])).
% 7.66/2.82  tff(c_7154, plain, (![A_251]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_251), u1_pre_topc(A_251)))=u1_struct_0(A_251) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_251), u1_pre_topc(A_251))) | ~l1_pre_topc(A_251))), inference(resolution, [status(thm)], [c_46, c_7137])).
% 7.66/2.82  tff(c_7163, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6930, c_7154])).
% 7.66/2.82  tff(c_7176, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7163])).
% 7.66/2.82  tff(c_7183, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_7176, c_6869])).
% 7.66/2.82  tff(c_7185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6867, c_7183])).
% 7.66/2.82  tff(c_7187, plain, (~v1_tops_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 7.66/2.82  tff(c_36, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2('#skF_2', '#skF_1') | v1_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_7194, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_7187, c_36])).
% 7.66/2.82  tff(c_7195, plain, (~v1_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_7194])).
% 7.66/2.82  tff(c_7186, plain, (v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_40])).
% 7.66/2.82  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | v1_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.66/2.82  tff(c_7196, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(negUnitSimplification, [status(thm)], [c_7187, c_38])).
% 7.66/2.82  tff(c_7239, plain, (![B_260, A_261]: (r1_tarski(B_260, u1_pre_topc(A_261)) | ~v1_tops_2(B_260, A_261) | ~m1_subset_1(B_260, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_261)))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.82  tff(c_7242, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_7196, c_7239])).
% 7.66/2.82  tff(c_7248, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7186, c_7242])).
% 7.66/2.82  tff(c_7251, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_7248])).
% 7.66/2.82  tff(c_7257, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_7251])).
% 7.66/2.82  tff(c_7263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_7257])).
% 7.66/2.82  tff(c_7265, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_7248])).
% 7.66/2.82  tff(c_7234, plain, (![C_256, A_257, D_258, B_259]: (C_256=A_257 | g1_pre_topc(C_256, D_258)!=g1_pre_topc(A_257, B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(k1_zfmisc_1(A_257))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_7236, plain, (![A_1, A_257, B_259]: (u1_struct_0(A_1)=A_257 | g1_pre_topc(A_257, B_259)!=A_1 | ~m1_subset_1(B_259, k1_zfmisc_1(k1_zfmisc_1(A_257))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7234])).
% 7.66/2.82  tff(c_7500, plain, (![A_280, B_281]: (u1_struct_0(g1_pre_topc(A_280, B_281))=A_280 | ~m1_subset_1(B_281, k1_zfmisc_1(k1_zfmisc_1(A_280))) | ~v1_pre_topc(g1_pre_topc(A_280, B_281)) | ~l1_pre_topc(g1_pre_topc(A_280, B_281)))), inference(reflexivity, [status(thm), theory('equality')], [c_7236])).
% 7.66/2.82  tff(c_7570, plain, (![A_282]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282)))=u1_struct_0(A_282) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_282), u1_pre_topc(A_282))) | ~l1_pre_topc(A_282))), inference(resolution, [status(thm)], [c_8, c_7500])).
% 7.66/2.82  tff(c_7588, plain, (![A_283]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_283), u1_pre_topc(A_283)))=u1_struct_0(A_283) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_283), u1_pre_topc(A_283))) | ~l1_pre_topc(A_283))), inference(resolution, [status(thm)], [c_46, c_7570])).
% 7.66/2.82  tff(c_7597, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7265, c_7588])).
% 7.66/2.82  tff(c_7610, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7597])).
% 7.66/2.82  tff(c_7617, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_7610, c_7196])).
% 7.66/2.82  tff(c_7686, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7617, c_14])).
% 7.66/2.82  tff(c_7704, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7686])).
% 7.66/2.82  tff(c_7705, plain, (~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_7195, c_7704])).
% 7.66/2.82  tff(c_7225, plain, (![D_252, B_253, C_254, A_255]: (D_252=B_253 | g1_pre_topc(C_254, D_252)!=g1_pre_topc(A_255, B_253) | ~m1_subset_1(B_253, k1_zfmisc_1(k1_zfmisc_1(A_255))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_7229, plain, (![A_1, D_252, C_254]: (u1_pre_topc(A_1)=D_252 | g1_pre_topc(C_254, D_252)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7225])).
% 7.66/2.82  tff(c_7770, plain, (![C_286, D_287]: (u1_pre_topc(g1_pre_topc(C_286, D_287))=D_287 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_286, D_287)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_286, D_287))))) | ~v1_pre_topc(g1_pre_topc(C_286, D_287)) | ~l1_pre_topc(g1_pre_topc(C_286, D_287)))), inference(reflexivity, [status(thm), theory('equality')], [c_7229])).
% 7.66/2.82  tff(c_7938, plain, (![C_290, D_291]: (u1_pre_topc(g1_pre_topc(C_290, D_291))=D_291 | ~v1_pre_topc(g1_pre_topc(C_290, D_291)) | ~l1_pre_topc(g1_pre_topc(C_290, D_291)))), inference(resolution, [status(thm)], [c_8, c_7770])).
% 7.66/2.82  tff(c_8143, plain, (![A_295]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_295), u1_pre_topc(A_295)))=u1_pre_topc(A_295) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_295), u1_pre_topc(A_295))) | ~l1_pre_topc(A_295))), inference(resolution, [status(thm)], [c_46, c_7938])).
% 7.66/2.82  tff(c_8161, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7265, c_8143])).
% 7.66/2.82  tff(c_8178, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8161])).
% 7.66/2.82  tff(c_7264, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_7248])).
% 7.66/2.82  tff(c_8187, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8178, c_7264])).
% 7.66/2.82  tff(c_8192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7705, c_8187])).
% 7.66/2.82  tff(c_8193, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_7194])).
% 7.66/2.82  tff(c_8204, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(negUnitSimplification, [status(thm)], [c_7187, c_38])).
% 7.66/2.82  tff(c_8239, plain, (![B_304, A_305]: (r1_tarski(B_304, u1_pre_topc(A_305)) | ~v1_tops_2(B_304, A_305) | ~m1_subset_1(B_304, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305)))) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.82  tff(c_8242, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_tops_2('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_8204, c_8239])).
% 7.66/2.82  tff(c_8248, plain, (r1_tarski('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7186, c_8242])).
% 7.66/2.82  tff(c_8251, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_8248])).
% 7.66/2.82  tff(c_8259, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_8251])).
% 7.66/2.82  tff(c_8265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_8259])).
% 7.66/2.82  tff(c_8267, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_8248])).
% 7.66/2.82  tff(c_8234, plain, (![D_300, B_301, C_302, A_303]: (D_300=B_301 | g1_pre_topc(C_302, D_300)!=g1_pre_topc(A_303, B_301) | ~m1_subset_1(B_301, k1_zfmisc_1(k1_zfmisc_1(A_303))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_8236, plain, (![A_1, B_301, A_303]: (u1_pre_topc(A_1)=B_301 | g1_pre_topc(A_303, B_301)!=A_1 | ~m1_subset_1(B_301, k1_zfmisc_1(k1_zfmisc_1(A_303))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8234])).
% 7.66/2.82  tff(c_8334, plain, (![A_322, B_323]: (u1_pre_topc(g1_pre_topc(A_322, B_323))=B_323 | ~m1_subset_1(B_323, k1_zfmisc_1(k1_zfmisc_1(A_322))) | ~v1_pre_topc(g1_pre_topc(A_322, B_323)) | ~l1_pre_topc(g1_pre_topc(A_322, B_323)))), inference(reflexivity, [status(thm), theory('equality')], [c_8236])).
% 7.66/2.82  tff(c_8607, plain, (![A_327]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_327), u1_pre_topc(A_327)))=u1_pre_topc(A_327) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_327), u1_pre_topc(A_327))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_327), u1_pre_topc(A_327))) | ~l1_pre_topc(A_327))), inference(resolution, [status(thm)], [c_8, c_8334])).
% 7.66/2.82  tff(c_8625, plain, (![A_328]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_328), u1_pre_topc(A_328)))=u1_pre_topc(A_328) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_328), u1_pre_topc(A_328))) | ~l1_pre_topc(A_328))), inference(resolution, [status(thm)], [c_46, c_8607])).
% 7.66/2.82  tff(c_8634, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8267, c_8625])).
% 7.66/2.82  tff(c_8647, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8634])).
% 7.66/2.82  tff(c_8677, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8647, c_8])).
% 7.66/2.82  tff(c_8700, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_8267, c_8677])).
% 7.66/2.82  tff(c_8199, plain, (![C_296, A_297, D_298, B_299]: (C_296=A_297 | g1_pre_topc(C_296, D_298)!=g1_pre_topc(A_297, B_299) | ~m1_subset_1(B_299, k1_zfmisc_1(k1_zfmisc_1(A_297))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.66/2.82  tff(c_8203, plain, (![A_1, C_296, D_298]: (u1_struct_0(A_1)=C_296 | g1_pre_topc(C_296, D_298)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8199])).
% 7.66/2.82  tff(c_8959, plain, (![C_335, D_336]: (u1_struct_0(g1_pre_topc(C_335, D_336))=C_335 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_335, D_336)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_335, D_336))))) | ~v1_pre_topc(g1_pre_topc(C_335, D_336)) | ~l1_pre_topc(g1_pre_topc(C_335, D_336)))), inference(reflexivity, [status(thm), theory('equality')], [c_8203])).
% 7.66/2.82  tff(c_8968, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8647, c_8959])).
% 7.66/2.82  tff(c_8987, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8267, c_8700, c_8968])).
% 7.66/2.82  tff(c_9030, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_8987])).
% 7.66/2.82  tff(c_9036, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_9030])).
% 7.66/2.82  tff(c_9042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_9036])).
% 7.66/2.82  tff(c_9043, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_8987])).
% 7.66/2.82  tff(c_9081, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_9043, c_8204])).
% 7.66/2.82  tff(c_9086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8193, c_9081])).
% 7.66/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.82  
% 7.66/2.82  Inference rules
% 7.66/2.82  ----------------------
% 7.66/2.82  #Ref     : 40
% 7.66/2.82  #Sup     : 1946
% 7.66/2.82  #Fact    : 0
% 7.66/2.82  #Define  : 0
% 7.66/2.82  #Split   : 48
% 7.66/2.82  #Chain   : 0
% 7.66/2.82  #Close   : 0
% 7.66/2.82  
% 7.66/2.82  Ordering : KBO
% 7.66/2.82  
% 7.66/2.82  Simplification rules
% 7.66/2.82  ----------------------
% 7.66/2.82  #Subsume      : 472
% 7.66/2.82  #Demod        : 3250
% 7.66/2.82  #Tautology    : 675
% 7.66/2.82  #SimpNegUnit  : 166
% 7.66/2.82  #BackRed      : 129
% 7.66/2.82  
% 7.66/2.82  #Partial instantiations: 0
% 7.66/2.82  #Strategies tried      : 1
% 7.66/2.82  
% 7.66/2.82  Timing (in seconds)
% 7.66/2.82  ----------------------
% 7.66/2.82  Preprocessing        : 0.42
% 7.66/2.82  Parsing              : 0.22
% 7.66/2.82  CNF conversion       : 0.03
% 7.66/2.82  Main loop            : 1.44
% 7.66/2.82  Inferencing          : 0.46
% 7.66/2.82  Reduction            : 0.53
% 7.66/2.82  Demodulation         : 0.39
% 7.66/2.82  BG Simplification    : 0.07
% 7.66/2.82  Subsumption          : 0.29
% 7.66/2.82  Abstraction          : 0.08
% 7.66/2.83  MUC search           : 0.00
% 7.66/2.83  Cooper               : 0.00
% 7.66/2.83  Total                : 1.94
% 7.66/2.83  Index Insertion      : 0.00
% 7.66/2.83  Index Deletion       : 0.00
% 7.66/2.83  Index Matching       : 0.00
% 7.66/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
