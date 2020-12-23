%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2020+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:46 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 292 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 943 expanded)
%              Number of equality atoms :   21 ( 310 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
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
                        & v1_tops_2(C,A) )
                     => v1_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_26,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ~ v1_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_160,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),B_67)
      | v1_tops_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66))))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_160])).

tff(c_173,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_166])).

tff(c_174,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_173])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),k1_zfmisc_1(u1_struct_0(A_1)))
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_14] :
      ( m1_subset_1(u1_pre_topc(A_14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,(
    ! [D_51,B_52,C_53,A_54] :
      ( D_51 = B_52
      | g1_pre_topc(C_53,D_51) != g1_pre_topc(A_54,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    ! [D_51,C_53] :
      ( u1_pre_topc('#skF_2') = D_51
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_53,D_51)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_85])).

tff(c_252,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_255,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_255])).

tff(c_260,plain,(
    ! [D_51,C_53] :
      ( u1_pre_topc('#skF_2') = D_51
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_53,D_51) ) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_296,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_260])).

tff(c_261,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_305,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_261])).

tff(c_76,plain,(
    ! [C_47,A_48,D_49,B_50] :
      ( C_47 = A_48
      | g1_pre_topc(C_47,D_49) != g1_pre_topc(A_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    ! [C_47,D_49] :
      ( u1_struct_0('#skF_2') = C_47
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_47,D_49)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_444,plain,(
    ! [C_47,D_49] :
      ( u1_struct_0('#skF_2') = C_47
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_47,D_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_296,c_80])).

tff(c_447,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_444])).

tff(c_24,plain,(
    v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_429,plain,(
    ! [C_88,A_89,B_90] :
      ( v3_pre_topc(C_88,A_89)
      | ~ r2_hidden(C_88,B_90)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v1_tops_2(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_591,plain,(
    ! [A_105] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_105)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v1_tops_2('#skF_4',A_105)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105))))
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_174,c_429])).

tff(c_598,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v1_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_591])).

tff(c_615,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_37,c_447,c_24,c_598])).

tff(c_647,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_653,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_647])).

tff(c_663,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37,c_653])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_663])).

tff(c_666,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    ! [A_36,C_37,B_38] :
      ( m1_subset_1(A_36,C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [A_36] :
      ( m1_subset_1(A_36,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_91,plain,(
    ! [B_58,A_59] :
      ( r2_hidden(B_58,u1_pre_topc(A_59))
      | ~ v3_pre_topc(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    ! [A_36] :
      ( r2_hidden(A_36,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_36,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_107,plain,(
    ! [A_36] :
      ( r2_hidden(A_36,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_36,'#skF_2')
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100])).

tff(c_400,plain,(
    ! [A_86] :
      ( r2_hidden(A_86,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_86,'#skF_2')
      | ~ r2_hidden(A_86,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_107])).

tff(c_53,plain,(
    ! [A_36] :
      ( m1_subset_1(A_36,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_37,c_44])).

tff(c_143,plain,(
    ! [B_64,A_65] :
      ( v3_pre_topc(B_64,A_65)
      | ~ r2_hidden(B_64,u1_pre_topc(A_65))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_36] :
      ( v3_pre_topc(A_36,'#skF_3')
      | ~ r2_hidden(A_36,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_53,c_143])).

tff(c_156,plain,(
    ! [A_36] :
      ( v3_pre_topc(A_36,'#skF_3')
      | ~ r2_hidden(A_36,u1_pre_topc('#skF_3'))
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_149])).

tff(c_417,plain,(
    ! [A_86] :
      ( v3_pre_topc(A_86,'#skF_3')
      | ~ v3_pre_topc(A_86,'#skF_2')
      | ~ r2_hidden(A_86,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_400,c_156])).

tff(c_672,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_666,c_417])).

tff(c_675,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_672])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_677,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_675,c_4])).

tff(c_680,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37,c_677])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_680])).

%------------------------------------------------------------------------------
