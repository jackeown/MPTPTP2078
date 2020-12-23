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
% DateTime   : Thu Dec  3 10:24:03 EST 2020

% Result     : Theorem 16.43s
% Output     : CNFRefutation 16.62s
% Verified   : 
% Statistics : Number of formulae       :  338 (4292 expanded)
%              Number of leaves         :   30 (1295 expanded)
%              Depth                    :   21
%              Number of atoms          :  791 (13000 expanded)
%              Number of equality atoms :  124 (1448 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( C = D
                   => ( v2_compts_1(C,A)
                    <=> v2_compts_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_113,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_16,plain,(
    ! [A_8] :
      ( m1_subset_1(u1_pre_topc(A_8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    ! [A_40,B_41] :
      ( l1_pre_topc(g1_pre_topc(A_40,B_41))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_8] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_8),u1_pre_topc(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_78,plain,(
    ! [A_44,B_45] :
      ( v1_pre_topc(g1_pre_topc(A_44,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_8] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_8),u1_pre_topc(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_78])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_242,plain,(
    ! [C_60,A_61,D_62,B_63] :
      ( C_60 = A_61
      | g1_pre_topc(C_60,D_62) != g1_pre_topc(A_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_244,plain,(
    ! [A_3,A_61,B_63] :
      ( u1_struct_0(A_3) = A_61
      | g1_pre_topc(A_61,B_63) != A_3
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_61)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_242])).

tff(c_6943,plain,(
    ! [A_280,B_281] :
      ( u1_struct_0(g1_pre_topc(A_280,B_281)) = A_280
      | ~ m1_subset_1(B_281,k1_zfmisc_1(k1_zfmisc_1(A_280)))
      | ~ v1_pre_topc(g1_pre_topc(A_280,B_281))
      | ~ l1_pre_topc(g1_pre_topc(A_280,B_281)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_244])).

tff(c_7896,plain,(
    ! [A_315] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_315),u1_pre_topc(A_315))) = u1_struct_0(A_315)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_315),u1_pre_topc(A_315)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_315),u1_pre_topc(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(resolution,[status(thm)],[c_16,c_6943])).

tff(c_8003,plain,(
    ! [A_318] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_318),u1_pre_topc(A_318))) = u1_struct_0(A_318)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_318),u1_pre_topc(A_318)))
      | ~ l1_pre_topc(A_318) ) ),
    inference(resolution,[status(thm)],[c_86,c_7896])).

tff(c_8047,plain,(
    ! [A_319] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_319),u1_pre_topc(A_319))) = u1_struct_0(A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(resolution,[status(thm)],[c_73,c_8003])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_409,plain,(
    ! [A_91,B_92] :
      ( u1_struct_0(g1_pre_topc(A_91,B_92)) = A_91
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91)))
      | ~ v1_pre_topc(g1_pre_topc(A_91,B_92))
      | ~ l1_pre_topc(g1_pre_topc(A_91,B_92)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_244])).

tff(c_1938,plain,(
    ! [A_165] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_165),u1_pre_topc(A_165))) = u1_struct_0(A_165)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_165),u1_pre_topc(A_165)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_165),u1_pre_topc(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_16,c_409])).

tff(c_1982,plain,(
    ! [A_166] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_166),u1_pre_topc(A_166))) = u1_struct_0(A_166)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_166),u1_pre_topc(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_86,c_1938])).

tff(c_2089,plain,(
    ! [A_168] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168))) = u1_struct_0(A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_73,c_1982])).

tff(c_52,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_77,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_281,plain,(
    ! [D_72,A_73,B_74] :
      ( v2_compts_1(D_72,A_73)
      | ~ v2_compts_1(D_72,B_74)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(u1_struct_0(B_74)))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_287,plain,(
    ! [A_73] :
      ( v2_compts_1('#skF_3',A_73)
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc('#skF_1',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_113,c_281])).

tff(c_293,plain,(
    ! [A_73] :
      ( v2_compts_1('#skF_3',A_73)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc('#skF_1',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_287])).

tff(c_2904,plain,(
    ! [A_177] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_293])).

tff(c_40,plain,
    ( v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_334,plain,(
    ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_2907,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2904,c_334])).

tff(c_2949,plain,
    ( ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_113,c_2907])).

tff(c_2957,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2949])).

tff(c_2963,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_2957])).

tff(c_2969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2963])).

tff(c_2971,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2949])).

tff(c_251,plain,(
    ! [D_64,B_65,C_66,A_67] :
      ( D_64 = B_65
      | g1_pre_topc(C_66,D_64) != g1_pre_topc(A_67,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_253,plain,(
    ! [A_3,B_65,A_67] :
      ( u1_pre_topc(A_3) = B_65
      | g1_pre_topc(A_67,B_65) != A_3
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_67)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_251])).

tff(c_1134,plain,(
    ! [A_133,B_134] :
      ( u1_pre_topc(g1_pre_topc(A_133,B_134)) = B_134
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_zfmisc_1(A_133)))
      | ~ v1_pre_topc(g1_pre_topc(A_133,B_134))
      | ~ l1_pre_topc(g1_pre_topc(A_133,B_134)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_253])).

tff(c_3381,plain,(
    ! [A_183] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183))) = u1_pre_topc(A_183)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(resolution,[status(thm)],[c_16,c_1134])).

tff(c_3434,plain,(
    ! [A_184] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_184),u1_pre_topc(A_184))) = u1_pre_topc(A_184)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_184),u1_pre_topc(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_86,c_3381])).

tff(c_3440,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2971,c_3434])).

tff(c_3485,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3440])).

tff(c_2209,plain,(
    ! [A_168] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_86])).

tff(c_3524,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3485,c_2209])).

tff(c_3576,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2971,c_3524])).

tff(c_2215,plain,(
    ! [A_168] :
      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_168))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_16])).

tff(c_3512,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3485,c_2215])).

tff(c_3568,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2971,c_3512])).

tff(c_275,plain,(
    ! [A_61,B_63] :
      ( u1_struct_0(g1_pre_topc(A_61,B_63)) = A_61
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_61)))
      | ~ v1_pre_topc(g1_pre_topc(A_61,B_63))
      | ~ l1_pre_topc(g1_pre_topc(A_61,B_63)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_244])).

tff(c_3609,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3568,c_275])).

tff(c_3621,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_3576,c_3609])).

tff(c_121,plain,(
    ! [A_52,B_53] :
      ( m1_pre_topc(k1_pre_topc(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,(
    ! [A_52] :
      ( m1_pre_topc(k1_pre_topc(A_52,u1_struct_0(A_52)),A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_53,c_121])).

tff(c_132,plain,(
    ! [B_55,A_56] :
      ( m1_pre_topc(B_55,A_56)
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_140,plain,(
    ! [A_56] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56)),u1_struct_0(g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56)))),A_56)
      | ~ l1_pre_topc(A_56)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56))) ) ),
    inference(resolution,[status(thm)],[c_130,c_132])).

tff(c_3704,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),u1_struct_0('#skF_1')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_140])).

tff(c_3871,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),u1_struct_0('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_30,c_3704])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_pre_topc(k1_pre_topc(A_6,B_7),A_6)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3791,plain,(
    ! [B_7] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_12])).

tff(c_3929,plain,(
    ! [B_7] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_3791])).

tff(c_141,plain,(
    ! [A_57,B_58] :
      ( u1_struct_0(k1_pre_topc(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_152,plain,(
    ! [A_57] :
      ( u1_struct_0(k1_pre_topc(A_57,u1_struct_0(A_57))) = u1_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_53,c_141])).

tff(c_378,plain,(
    ! [D_82,B_83,A_84] :
      ( v2_compts_1(D_82,B_83)
      | ~ v2_compts_1(D_82,A_84)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(u1_struct_0(B_83)))
      | ~ m1_subset_1(D_82,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5213,plain,(
    ! [D_204,A_205,A_206] :
      ( v2_compts_1(D_204,k1_pre_topc(A_205,u1_struct_0(A_205)))
      | ~ v2_compts_1(D_204,A_206)
      | ~ m1_subset_1(D_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(D_204,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ m1_pre_topc(k1_pre_topc(A_205,u1_struct_0(A_205)),A_206)
      | ~ l1_pre_topc(A_206)
      | ~ l1_pre_topc(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_378])).

tff(c_5245,plain,(
    ! [A_205] :
      ( v2_compts_1('#skF_3',k1_pre_topc(A_205,u1_struct_0(A_205)))
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_pre_topc(k1_pre_topc(A_205,u1_struct_0(A_205)),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_113,c_5213])).

tff(c_5255,plain,(
    ! [A_205] :
      ( v2_compts_1('#skF_3',k1_pre_topc(A_205,u1_struct_0(A_205)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_pre_topc(k1_pre_topc(A_205,u1_struct_0(A_205)),'#skF_1')
      | ~ l1_pre_topc(A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77,c_5245])).

tff(c_5754,plain,(
    ! [D_214,A_215,A_216] :
      ( v2_compts_1(D_214,A_215)
      | ~ v2_compts_1(D_214,k1_pre_topc(A_216,u1_struct_0(A_216)))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ m1_pre_topc(k1_pre_topc(A_216,u1_struct_0(A_216)),A_215)
      | ~ l1_pre_topc(A_215)
      | ~ l1_pre_topc(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_281])).

tff(c_5826,plain,(
    ! [A_217,A_218] :
      ( v2_compts_1('#skF_3',A_217)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ m1_pre_topc(k1_pre_topc(A_218,u1_struct_0(A_218)),A_217)
      | ~ l1_pre_topc(A_217)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_pre_topc(k1_pre_topc(A_218,u1_struct_0(A_218)),'#skF_1')
      | ~ l1_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_5255,c_5754])).

tff(c_5832,plain,(
    ! [A_218] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(k1_pre_topc(A_218,u1_struct_0(A_218)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_pre_topc(k1_pre_topc(A_218,u1_struct_0(A_218)),'#skF_1')
      | ~ l1_pre_topc(A_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_5826])).

tff(c_5862,plain,(
    ! [A_218] :
      ( v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(k1_pre_topc(A_218,u1_struct_0(A_218)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_pre_topc(k1_pre_topc(A_218,u1_struct_0(A_218)),'#skF_1')
      | ~ l1_pre_topc(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_113,c_5832])).

tff(c_6182,plain,(
    ! [A_228] :
      ( ~ m1_pre_topc(k1_pre_topc(A_228,u1_struct_0(A_228)),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_pre_topc(k1_pre_topc(A_228,u1_struct_0(A_228)),'#skF_1')
      | ~ l1_pre_topc(A_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_5862])).

tff(c_6186,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))),'#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3929,c_6182])).

tff(c_6246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_3621,c_2971,c_3871,c_3621,c_113,c_3621,c_6186])).

tff(c_6247,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6254,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_6247])).

tff(c_8139,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8047,c_6254])).

tff(c_8231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_113,c_8139])).

tff(c_8233,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_6247])).

tff(c_6248,plain,(
    v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8240,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6248,c_36])).

tff(c_8241,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_8240])).

tff(c_8270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8233,c_8241])).

tff(c_8271,plain,
    ( ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8240])).

tff(c_8274,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8271])).

tff(c_8272,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_8240])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( v1_pre_topc(k1_pre_topc(A_6,B_7))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8298,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8272,c_14])).

tff(c_8326,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8298])).

tff(c_8332,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_8326])).

tff(c_8338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8332])).

tff(c_8340,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8298])).

tff(c_8663,plain,(
    ! [A_333,B_334] :
      ( u1_pre_topc(g1_pre_topc(A_333,B_334)) = B_334
      | ~ m1_subset_1(B_334,k1_zfmisc_1(k1_zfmisc_1(A_333)))
      | ~ v1_pre_topc(g1_pre_topc(A_333,B_334))
      | ~ l1_pre_topc(g1_pre_topc(A_333,B_334)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_253])).

tff(c_10242,plain,(
    ! [A_400] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_400),u1_pre_topc(A_400))) = u1_pre_topc(A_400)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_400),u1_pre_topc(A_400)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_400),u1_pre_topc(A_400)))
      | ~ l1_pre_topc(A_400) ) ),
    inference(resolution,[status(thm)],[c_16,c_8663])).

tff(c_10294,plain,(
    ! [A_401] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401))) = u1_pre_topc(A_401)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401)))
      | ~ l1_pre_topc(A_401) ) ),
    inference(resolution,[status(thm)],[c_86,c_10242])).

tff(c_10327,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8340,c_10294])).

tff(c_10349,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10327])).

tff(c_10418,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10349,c_16])).

tff(c_10439,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8340,c_10418])).

tff(c_10409,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10349,c_6])).

tff(c_10433,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8340,c_10409])).

tff(c_11404,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_10433])).

tff(c_11410,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_11404])).

tff(c_11416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_11410])).

tff(c_11417,plain,(
    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10433])).

tff(c_20,plain,(
    ! [C_13,A_9,D_14,B_10] :
      ( C_13 = A_9
      | g1_pre_topc(C_13,D_14) != g1_pre_topc(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_11462,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_13
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_13,D_14)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11417,c_20])).

tff(c_11479,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_13
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10439,c_11462])).

tff(c_11657,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11479])).

tff(c_38,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_compts_1('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8302,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6248,c_8272,c_38])).

tff(c_11676,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_8302])).

tff(c_11679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8274,c_11676])).

tff(c_11680,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_8271])).

tff(c_11681,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8271])).

tff(c_11683,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6248,c_38])).

tff(c_11684,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_11683])).

tff(c_11793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8233,c_11684])).

tff(c_11795,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_11683])).

tff(c_11819,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_11795,c_14])).

tff(c_11925,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11819])).

tff(c_11931,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_11925])).

tff(c_11937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_11931])).

tff(c_11939,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_11819])).

tff(c_12323,plain,(
    ! [A_433,B_434] :
      ( u1_struct_0(g1_pre_topc(A_433,B_434)) = A_433
      | ~ m1_subset_1(B_434,k1_zfmisc_1(k1_zfmisc_1(A_433)))
      | ~ v1_pre_topc(g1_pre_topc(A_433,B_434))
      | ~ l1_pre_topc(g1_pre_topc(A_433,B_434)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_244])).

tff(c_14277,plain,(
    ! [A_508] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_508),u1_pre_topc(A_508))) = u1_struct_0(A_508)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_508),u1_pre_topc(A_508)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_508),u1_pre_topc(A_508)))
      | ~ l1_pre_topc(A_508) ) ),
    inference(resolution,[status(thm)],[c_16,c_12323])).

tff(c_14333,plain,(
    ! [A_509] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_509),u1_pre_topc(A_509))) = u1_struct_0(A_509)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_509),u1_pre_topc(A_509)))
      | ~ l1_pre_topc(A_509) ) ),
    inference(resolution,[status(thm)],[c_86,c_14277])).

tff(c_14366,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_11939,c_14333])).

tff(c_14391,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14366])).

tff(c_14511,plain,(
    ! [B_7] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14391,c_12])).

tff(c_16494,plain,(
    ! [B_526] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_526),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_526,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11939,c_14511])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( m1_pre_topc(B_20,A_18)
      | ~ m1_pre_topc(B_20,g1_pre_topc(u1_struct_0(A_18),u1_pre_topc(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16497,plain,(
    ! [B_526] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_526),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_526,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_16494,c_24])).

tff(c_16506,plain,(
    ! [B_526] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_526),'#skF_1')
      | ~ m1_subset_1(B_526,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16497])).

tff(c_8232,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6247])).

tff(c_14606,plain,(
    ! [B_7] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11939,c_14511])).

tff(c_11794,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_11683])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( u1_struct_0(k1_pre_topc(A_15,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11920,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_11794,c_22])).

tff(c_12090,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11939,c_11920])).

tff(c_12729,plain,(
    ! [B_447,A_448] :
      ( v2_compts_1(u1_struct_0(B_447),A_448)
      | ~ v2_compts_1(u1_struct_0(B_447),B_447)
      | ~ m1_subset_1(u1_struct_0(B_447),k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ m1_pre_topc(B_447,A_448)
      | ~ l1_pre_topc(A_448) ) ),
    inference(resolution,[status(thm)],[c_53,c_281])).

tff(c_12737,plain,(
    ! [A_448] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_448)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_448)
      | ~ l1_pre_topc(A_448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12090,c_12729])).

tff(c_12749,plain,(
    ! [A_448] :
      ( v2_compts_1('#skF_2',A_448)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_448)
      | ~ l1_pre_topc(A_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12090,c_12090,c_12737])).

tff(c_21297,plain,(
    ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12749])).

tff(c_11951,plain,(
    ! [D_419,B_420,A_421] :
      ( v2_compts_1(D_419,B_420)
      | ~ v2_compts_1(D_419,A_421)
      | ~ m1_subset_1(D_419,k1_zfmisc_1(u1_struct_0(B_420)))
      | ~ m1_subset_1(D_419,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12456,plain,(
    ! [B_436,A_437] :
      ( v2_compts_1(u1_struct_0(B_436),B_436)
      | ~ v2_compts_1(u1_struct_0(B_436),A_437)
      | ~ m1_subset_1(u1_struct_0(B_436),k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(resolution,[status(thm)],[c_53,c_11951])).

tff(c_12462,plain,(
    ! [A_437] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_437)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12090,c_12456])).

tff(c_12487,plain,(
    ! [A_437] :
      ( v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_437)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12090,c_12090,c_12462])).

tff(c_21928,plain,(
    ! [A_605] :
      ( ~ v2_compts_1('#skF_2',A_605)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_605)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_605)
      | ~ l1_pre_topc(A_605) ) ),
    inference(negUnitSimplification,[status(thm)],[c_21297,c_12487])).

tff(c_21936,plain,
    ( ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14606,c_21928])).

tff(c_21952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11681,c_11939,c_11681,c_14391,c_8232,c_21936])).

tff(c_21961,plain,(
    ! [A_606] :
      ( v2_compts_1('#skF_2',A_606)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_606)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_606)
      | ~ l1_pre_topc(A_606) ) ),
    inference(splitRight,[status(thm)],[c_12749])).

tff(c_21965,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16506,c_21961])).

tff(c_21981,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11681,c_30,c_21965])).

tff(c_21983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11680,c_21981])).

tff(c_21985,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22067,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_21985,c_42])).

tff(c_22068,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22067])).

tff(c_44,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22078,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_21985,c_44])).

tff(c_22092,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22078,c_14])).

tff(c_22095,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_22092])).

tff(c_22101,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_22095])).

tff(c_22107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22101])).

tff(c_22109,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22092])).

tff(c_22073,plain,(
    ! [C_619,A_620,D_621,B_622] :
      ( C_619 = A_620
      | g1_pre_topc(C_619,D_621) != g1_pre_topc(A_620,B_622)
      | ~ m1_subset_1(B_622,k1_zfmisc_1(k1_zfmisc_1(A_620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22075,plain,(
    ! [A_3,A_620,B_622] :
      ( u1_struct_0(A_3) = A_620
      | g1_pre_topc(A_620,B_622) != A_3
      | ~ m1_subset_1(B_622,k1_zfmisc_1(k1_zfmisc_1(A_620)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_22073])).

tff(c_22304,plain,(
    ! [A_646,B_647] :
      ( u1_struct_0(g1_pre_topc(A_646,B_647)) = A_646
      | ~ m1_subset_1(B_647,k1_zfmisc_1(k1_zfmisc_1(A_646)))
      | ~ v1_pre_topc(g1_pre_topc(A_646,B_647))
      | ~ l1_pre_topc(g1_pre_topc(A_646,B_647)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22075])).

tff(c_23766,plain,(
    ! [A_708] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_708),u1_pre_topc(A_708))) = u1_struct_0(A_708)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_708),u1_pre_topc(A_708)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_708),u1_pre_topc(A_708)))
      | ~ l1_pre_topc(A_708) ) ),
    inference(resolution,[status(thm)],[c_16,c_22304])).

tff(c_23810,plain,(
    ! [A_709] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_709),u1_pre_topc(A_709))) = u1_struct_0(A_709)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_709),u1_pre_topc(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(resolution,[status(thm)],[c_86,c_23766])).

tff(c_23840,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22109,c_23810])).

tff(c_23858,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_23840])).

tff(c_23860,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23858,c_22078])).

tff(c_22090,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22078,c_12])).

tff(c_22529,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22109,c_22090])).

tff(c_22532,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22529,c_24])).

tff(c_22541,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22532])).

tff(c_21984,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_22091,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22078,c_22])).

tff(c_22133,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22109,c_22091])).

tff(c_22244,plain,(
    ! [D_635,B_636,A_637] :
      ( v2_compts_1(D_635,B_636)
      | ~ v2_compts_1(D_635,A_637)
      | ~ m1_subset_1(D_635,k1_zfmisc_1(u1_struct_0(B_636)))
      | ~ m1_subset_1(D_635,k1_zfmisc_1(u1_struct_0(A_637)))
      | ~ m1_pre_topc(B_636,A_637)
      | ~ l1_pre_topc(A_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22837,plain,(
    ! [B_669,A_670] :
      ( v2_compts_1(u1_struct_0(B_669),B_669)
      | ~ v2_compts_1(u1_struct_0(B_669),A_670)
      | ~ m1_subset_1(u1_struct_0(B_669),k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ m1_pre_topc(B_669,A_670)
      | ~ l1_pre_topc(A_670) ) ),
    inference(resolution,[status(thm)],[c_53,c_22244])).

tff(c_22851,plain,(
    ! [A_670] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_670)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_670)
      | ~ l1_pre_topc(A_670) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22133,c_22837])).

tff(c_22865,plain,(
    ! [A_670] :
      ( v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_670)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_670)
      | ~ l1_pre_topc(A_670) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22133,c_22133,c_22851])).

tff(c_26149,plain,(
    ! [A_736] :
      ( ~ v2_compts_1('#skF_2',A_736)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_736)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_736)
      | ~ l1_pre_topc(A_736) ) ),
    inference(splitLeft,[status(thm)],[c_22865])).

tff(c_26155,plain,
    ( ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22529,c_26149])).

tff(c_26165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22109,c_23860,c_23858,c_21984,c_26155])).

tff(c_26166,plain,(
    v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_22865])).

tff(c_22110,plain,(
    ! [D_623,A_624,B_625] :
      ( v2_compts_1(D_623,A_624)
      | ~ v2_compts_1(D_623,B_625)
      | ~ m1_subset_1(D_623,k1_zfmisc_1(u1_struct_0(B_625)))
      | ~ m1_subset_1(D_623,k1_zfmisc_1(u1_struct_0(A_624)))
      | ~ m1_pre_topc(B_625,A_624)
      | ~ l1_pre_topc(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22701,plain,(
    ! [B_658,A_659] :
      ( v2_compts_1(u1_struct_0(B_658),A_659)
      | ~ v2_compts_1(u1_struct_0(B_658),B_658)
      | ~ m1_subset_1(u1_struct_0(B_658),k1_zfmisc_1(u1_struct_0(A_659)))
      | ~ m1_pre_topc(B_658,A_659)
      | ~ l1_pre_topc(A_659) ) ),
    inference(resolution,[status(thm)],[c_53,c_22110])).

tff(c_22707,plain,(
    ! [A_659] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_659)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_659)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_659)
      | ~ l1_pre_topc(A_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22133,c_22701])).

tff(c_22712,plain,(
    ! [A_659] :
      ( v2_compts_1('#skF_2',A_659)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_659)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_659)
      | ~ l1_pre_topc(A_659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22133,c_22133,c_22707])).

tff(c_26179,plain,(
    ! [A_740] :
      ( v2_compts_1('#skF_2',A_740)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_740)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_740)
      | ~ l1_pre_topc(A_740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26166,c_22712])).

tff(c_26182,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22541,c_26179])).

tff(c_26191,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_23860,c_26182])).

tff(c_26193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22068,c_26191])).

tff(c_26194,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22067])).

tff(c_26205,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_21985,c_44])).

tff(c_26219,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26205,c_14])).

tff(c_26223,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_26219])).

tff(c_26229,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_26223])).

tff(c_26235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26229])).

tff(c_26237,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_26219])).

tff(c_22062,plain,(
    ! [D_615,B_616,C_617,A_618] :
      ( D_615 = B_616
      | g1_pre_topc(C_617,D_615) != g1_pre_topc(A_618,B_616)
      | ~ m1_subset_1(B_616,k1_zfmisc_1(k1_zfmisc_1(A_618))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22064,plain,(
    ! [A_3,B_616,A_618] :
      ( u1_pre_topc(A_3) = B_616
      | g1_pre_topc(A_618,B_616) != A_3
      | ~ m1_subset_1(B_616,k1_zfmisc_1(k1_zfmisc_1(A_618)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_22062])).

tff(c_26430,plain,(
    ! [A_768,B_769] :
      ( u1_pre_topc(g1_pre_topc(A_768,B_769)) = B_769
      | ~ m1_subset_1(B_769,k1_zfmisc_1(k1_zfmisc_1(A_768)))
      | ~ v1_pre_topc(g1_pre_topc(A_768,B_769))
      | ~ l1_pre_topc(g1_pre_topc(A_768,B_769)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22064])).

tff(c_27685,plain,(
    ! [A_827] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_827),u1_pre_topc(A_827))) = u1_pre_topc(A_827)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_827),u1_pre_topc(A_827)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_827),u1_pre_topc(A_827)))
      | ~ l1_pre_topc(A_827) ) ),
    inference(resolution,[status(thm)],[c_16,c_26430])).

tff(c_27729,plain,(
    ! [A_828] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_828),u1_pre_topc(A_828))) = u1_pre_topc(A_828)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_828),u1_pre_topc(A_828)))
      | ~ l1_pre_topc(A_828) ) ),
    inference(resolution,[status(thm)],[c_86,c_27685])).

tff(c_27759,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26237,c_27729])).

tff(c_27777,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_27759])).

tff(c_27803,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27777,c_16])).

tff(c_27824,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26237,c_27803])).

tff(c_27794,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27777,c_6])).

tff(c_27818,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26237,c_27794])).

tff(c_28648,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_27818])).

tff(c_28654,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_28648])).

tff(c_28660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28654])).

tff(c_28661,plain,(
    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_27818])).

tff(c_28786,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_13
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_13,D_14)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28661,c_20])).

tff(c_28807,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_13
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27824,c_28786])).

tff(c_28854,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_28807])).

tff(c_28871,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28854,c_26205])).

tff(c_28873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26194,c_28871])).

tff(c_28875,plain,(
    ~ v2_compts_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28887,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_28875,c_48])).

tff(c_28888,plain,(
    ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28887])).

tff(c_50,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28984,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_28875,c_50])).

tff(c_28998,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28984,c_14])).

tff(c_29020,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28998])).

tff(c_29026,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_29020])).

tff(c_29032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_29026])).

tff(c_29034,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28998])).

tff(c_28876,plain,(
    ! [A_847,B_848] :
      ( v1_pre_topc(g1_pre_topc(A_847,B_848))
      | ~ m1_subset_1(B_848,k1_zfmisc_1(k1_zfmisc_1(A_847))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28884,plain,(
    ! [A_8] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_8),u1_pre_topc(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_28876])).

tff(c_29014,plain,(
    ! [D_867,B_868,C_869,A_870] :
      ( D_867 = B_868
      | g1_pre_topc(C_869,D_867) != g1_pre_topc(A_870,B_868)
      | ~ m1_subset_1(B_868,k1_zfmisc_1(k1_zfmisc_1(A_870))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29016,plain,(
    ! [A_3,B_868,A_870] :
      ( u1_pre_topc(A_3) = B_868
      | g1_pre_topc(A_870,B_868) != A_3
      | ~ m1_subset_1(B_868,k1_zfmisc_1(k1_zfmisc_1(A_870)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_29014])).

tff(c_29860,plain,(
    ! [A_931,B_932] :
      ( u1_pre_topc(g1_pre_topc(A_931,B_932)) = B_932
      | ~ m1_subset_1(B_932,k1_zfmisc_1(k1_zfmisc_1(A_931)))
      | ~ v1_pre_topc(g1_pre_topc(A_931,B_932))
      | ~ l1_pre_topc(g1_pre_topc(A_931,B_932)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_29016])).

tff(c_30611,plain,(
    ! [A_955] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_955),u1_pre_topc(A_955))) = u1_pre_topc(A_955)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_955),u1_pre_topc(A_955)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_955),u1_pre_topc(A_955)))
      | ~ l1_pre_topc(A_955) ) ),
    inference(resolution,[status(thm)],[c_16,c_29860])).

tff(c_30655,plain,(
    ! [A_956] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_956),u1_pre_topc(A_956))) = u1_pre_topc(A_956)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_956),u1_pre_topc(A_956)))
      | ~ l1_pre_topc(A_956) ) ),
    inference(resolution,[status(thm)],[c_28884,c_30611])).

tff(c_30685,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_29034,c_30655])).

tff(c_30703,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30685])).

tff(c_30723,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30703,c_6])).

tff(c_30749,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29034,c_30723])).

tff(c_31733,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_30749])).

tff(c_31739,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28884,c_31733])).

tff(c_31745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_31739])).

tff(c_31747,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_30749])).

tff(c_29005,plain,(
    ! [C_863,A_864,D_865,B_866] :
      ( C_863 = A_864
      | g1_pre_topc(C_863,D_865) != g1_pre_topc(A_864,B_866)
      | ~ m1_subset_1(B_866,k1_zfmisc_1(k1_zfmisc_1(A_864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29009,plain,(
    ! [A_3,C_863,D_865] :
      ( u1_struct_0(A_3) = C_863
      | g1_pre_topc(C_863,D_865) != A_3
      | ~ m1_subset_1(u1_pre_topc(A_3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_29005])).

tff(c_31748,plain,(
    ! [C_970,D_971] :
      ( u1_struct_0(g1_pre_topc(C_970,D_971)) = C_970
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_970,D_971)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_970,D_971)))))
      | ~ v1_pre_topc(g1_pre_topc(C_970,D_971))
      | ~ l1_pre_topc(g1_pre_topc(C_970,D_971)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_29009])).

tff(c_31799,plain,(
    ! [C_972,D_973] :
      ( u1_struct_0(g1_pre_topc(C_972,D_973)) = C_972
      | ~ v1_pre_topc(g1_pre_topc(C_972,D_973))
      | ~ l1_pre_topc(g1_pre_topc(C_972,D_973)) ) ),
    inference(resolution,[status(thm)],[c_16,c_31748])).

tff(c_31802,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_31747,c_31799])).

tff(c_31829,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29034,c_31802])).

tff(c_31848,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31829,c_28984])).

tff(c_28996,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28984,c_12])).

tff(c_29616,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29034,c_28996])).

tff(c_29619,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_29616,c_24])).

tff(c_29628,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_29619])).

tff(c_28874,plain,(
    v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_28997,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28984,c_22])).

tff(c_29047,plain,(
    u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29034,c_28997])).

tff(c_29116,plain,(
    ! [D_875,B_876,A_877] :
      ( v2_compts_1(D_875,B_876)
      | ~ v2_compts_1(D_875,A_877)
      | ~ m1_subset_1(D_875,k1_zfmisc_1(u1_struct_0(B_876)))
      | ~ m1_subset_1(D_875,k1_zfmisc_1(u1_struct_0(A_877)))
      | ~ m1_pre_topc(B_876,A_877)
      | ~ l1_pre_topc(A_877) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_29824,plain,(
    ! [B_926,A_927] :
      ( v2_compts_1(u1_struct_0(B_926),B_926)
      | ~ v2_compts_1(u1_struct_0(B_926),A_927)
      | ~ m1_subset_1(u1_struct_0(B_926),k1_zfmisc_1(u1_struct_0(A_927)))
      | ~ m1_pre_topc(B_926,A_927)
      | ~ l1_pre_topc(A_927) ) ),
    inference(resolution,[status(thm)],[c_53,c_29116])).

tff(c_29838,plain,(
    ! [A_927] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_927)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_927)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_927)
      | ~ l1_pre_topc(A_927) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29047,c_29824])).

tff(c_29852,plain,(
    ! [A_927] :
      ( v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_927)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_927)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_927)
      | ~ l1_pre_topc(A_927) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29047,c_29047,c_29838])).

tff(c_32913,plain,(
    ! [A_980] :
      ( ~ v2_compts_1('#skF_2',A_980)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_980)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_980)
      | ~ l1_pre_topc(A_980) ) ),
    inference(splitLeft,[status(thm)],[c_29852])).

tff(c_32919,plain,
    ( ~ v2_compts_1('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_29616,c_32913])).

tff(c_32929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29034,c_31848,c_31829,c_28874,c_32919])).

tff(c_32930,plain,(
    v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29852])).

tff(c_29330,plain,(
    ! [D_893,A_894,B_895] :
      ( v2_compts_1(D_893,A_894)
      | ~ v2_compts_1(D_893,B_895)
      | ~ m1_subset_1(D_893,k1_zfmisc_1(u1_struct_0(B_895)))
      | ~ m1_subset_1(D_893,k1_zfmisc_1(u1_struct_0(A_894)))
      | ~ m1_pre_topc(B_895,A_894)
      | ~ l1_pre_topc(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_29735,plain,(
    ! [B_913,A_914] :
      ( v2_compts_1(u1_struct_0(B_913),A_914)
      | ~ v2_compts_1(u1_struct_0(B_913),B_913)
      | ~ m1_subset_1(u1_struct_0(B_913),k1_zfmisc_1(u1_struct_0(A_914)))
      | ~ m1_pre_topc(B_913,A_914)
      | ~ l1_pre_topc(A_914) ) ),
    inference(resolution,[status(thm)],[c_53,c_29330])).

tff(c_29743,plain,(
    ! [A_914] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),A_914)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_914)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_914)
      | ~ l1_pre_topc(A_914) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29047,c_29735])).

tff(c_29748,plain,(
    ! [A_914] :
      ( v2_compts_1('#skF_2',A_914)
      | ~ v2_compts_1('#skF_2',k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_914)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_914)
      | ~ l1_pre_topc(A_914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29047,c_29047,c_29743])).

tff(c_33143,plain,(
    ! [A_983] :
      ( v2_compts_1('#skF_2',A_983)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_983)))
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'),A_983)
      | ~ l1_pre_topc(A_983) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32930,c_29748])).

tff(c_33146,plain,
    ( v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_29628,c_33143])).

tff(c_33155,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_31848,c_33146])).

tff(c_33157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28888,c_33155])).

tff(c_33158,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28887])).

tff(c_33254,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_28875,c_50])).

tff(c_33268,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_33254,c_14])).

tff(c_33293,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_33268])).

tff(c_33310,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_33293])).

tff(c_33316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_33310])).

tff(c_33318,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_33268])).

tff(c_33287,plain,(
    ! [D_1001,B_1002,C_1003,A_1004] :
      ( D_1001 = B_1002
      | g1_pre_topc(C_1003,D_1001) != g1_pre_topc(A_1004,B_1002)
      | ~ m1_subset_1(B_1002,k1_zfmisc_1(k1_zfmisc_1(A_1004))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33289,plain,(
    ! [A_3,B_1002,A_1004] :
      ( u1_pre_topc(A_3) = B_1002
      | g1_pre_topc(A_1004,B_1002) != A_3
      | ~ m1_subset_1(B_1002,k1_zfmisc_1(k1_zfmisc_1(A_1004)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33287])).

tff(c_33501,plain,(
    ! [A_1027,B_1028] :
      ( u1_pre_topc(g1_pre_topc(A_1027,B_1028)) = B_1028
      | ~ m1_subset_1(B_1028,k1_zfmisc_1(k1_zfmisc_1(A_1027)))
      | ~ v1_pre_topc(g1_pre_topc(A_1027,B_1028))
      | ~ l1_pre_topc(g1_pre_topc(A_1027,B_1028)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33289])).

tff(c_34895,plain,(
    ! [A_1092] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1092),u1_pre_topc(A_1092))) = u1_pre_topc(A_1092)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1092),u1_pre_topc(A_1092)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1092),u1_pre_topc(A_1092)))
      | ~ l1_pre_topc(A_1092) ) ),
    inference(resolution,[status(thm)],[c_16,c_33501])).

tff(c_35002,plain,(
    ! [A_1095] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1095),u1_pre_topc(A_1095))) = u1_pre_topc(A_1095)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1095),u1_pre_topc(A_1095)))
      | ~ l1_pre_topc(A_1095) ) ),
    inference(resolution,[status(thm)],[c_28884,c_34895])).

tff(c_35032,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33318,c_35002])).

tff(c_35050,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35032])).

tff(c_35082,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35050,c_16])).

tff(c_35107,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33318,c_35082])).

tff(c_33278,plain,(
    ! [C_997,A_998,D_999,B_1000] :
      ( C_997 = A_998
      | g1_pre_topc(C_997,D_999) != g1_pre_topc(A_998,B_1000)
      | ~ m1_subset_1(B_1000,k1_zfmisc_1(k1_zfmisc_1(A_998))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33282,plain,(
    ! [A_3,C_997,D_999] :
      ( u1_struct_0(A_3) = C_997
      | g1_pre_topc(C_997,D_999) != A_3
      | ~ m1_subset_1(u1_pre_topc(A_3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33278])).

tff(c_35705,plain,(
    ! [C_1099,D_1100] :
      ( u1_struct_0(g1_pre_topc(C_1099,D_1100)) = C_1099
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_1099,D_1100)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1099,D_1100)))))
      | ~ v1_pre_topc(g1_pre_topc(C_1099,D_1100))
      | ~ l1_pre_topc(g1_pre_topc(C_1099,D_1100)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33282])).

tff(c_35717,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35050,c_35705])).

tff(c_35738,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33318,c_35107,c_35717])).

tff(c_35776,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_35738])).

tff(c_35782,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28884,c_35776])).

tff(c_35788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35782])).

tff(c_35789,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_35738])).

tff(c_35809,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35789,c_33254])).

tff(c_35814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33158,c_35809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.43/7.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.62/7.07  
% 16.62/7.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.62/7.07  %$ v2_compts_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 16.62/7.07  
% 16.62/7.07  %Foreground sorts:
% 16.62/7.07  
% 16.62/7.07  
% 16.62/7.07  %Background operators:
% 16.62/7.07  
% 16.62/7.07  
% 16.62/7.07  %Foreground operators:
% 16.62/7.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.62/7.07  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 16.62/7.07  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 16.62/7.07  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.62/7.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.62/7.07  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 16.62/7.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.62/7.07  tff('#skF_2', type, '#skF_2': $i).
% 16.62/7.07  tff('#skF_3', type, '#skF_3': $i).
% 16.62/7.07  tff('#skF_1', type, '#skF_1': $i).
% 16.62/7.07  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.62/7.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.62/7.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.62/7.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.62/7.07  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.62/7.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.62/7.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.62/7.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 16.62/7.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.62/7.07  
% 16.62/7.12  tff(f_110, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_compts_1(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v2_compts_1(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_compts_1)).
% 16.62/7.12  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 16.62/7.12  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 16.62/7.12  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 16.62/7.12  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 16.62/7.12  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 16.62/7.12  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 16.62/7.12  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_compts_1)).
% 16.62/7.12  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 16.62/7.12  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 16.62/7.12  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 16.62/7.12  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_46, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_113, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_46])).
% 16.62/7.12  tff(c_16, plain, (![A_8]: (m1_subset_1(u1_pre_topc(A_8), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.62/7.12  tff(c_65, plain, (![A_40, B_41]: (l1_pre_topc(g1_pre_topc(A_40, B_41)) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.62/7.12  tff(c_73, plain, (![A_8]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_8), u1_pre_topc(A_8))) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_16, c_65])).
% 16.62/7.12  tff(c_78, plain, (![A_44, B_45]: (v1_pre_topc(g1_pre_topc(A_44, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.62/7.12  tff(c_86, plain, (![A_8]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_8), u1_pre_topc(A_8))) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_16, c_78])).
% 16.62/7.12  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.62/7.12  tff(c_242, plain, (![C_60, A_61, D_62, B_63]: (C_60=A_61 | g1_pre_topc(C_60, D_62)!=g1_pre_topc(A_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_244, plain, (![A_3, A_61, B_63]: (u1_struct_0(A_3)=A_61 | g1_pre_topc(A_61, B_63)!=A_3 | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_61))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_242])).
% 16.62/7.12  tff(c_6943, plain, (![A_280, B_281]: (u1_struct_0(g1_pre_topc(A_280, B_281))=A_280 | ~m1_subset_1(B_281, k1_zfmisc_1(k1_zfmisc_1(A_280))) | ~v1_pre_topc(g1_pre_topc(A_280, B_281)) | ~l1_pre_topc(g1_pre_topc(A_280, B_281)))), inference(reflexivity, [status(thm), theory('equality')], [c_244])).
% 16.62/7.12  tff(c_7896, plain, (![A_315]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_315), u1_pre_topc(A_315)))=u1_struct_0(A_315) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_315), u1_pre_topc(A_315))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_315), u1_pre_topc(A_315))) | ~l1_pre_topc(A_315))), inference(resolution, [status(thm)], [c_16, c_6943])).
% 16.62/7.12  tff(c_8003, plain, (![A_318]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_318), u1_pre_topc(A_318)))=u1_struct_0(A_318) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_318), u1_pre_topc(A_318))) | ~l1_pre_topc(A_318))), inference(resolution, [status(thm)], [c_86, c_7896])).
% 16.62/7.12  tff(c_8047, plain, (![A_319]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_319), u1_pre_topc(A_319)))=u1_struct_0(A_319) | ~l1_pre_topc(A_319))), inference(resolution, [status(thm)], [c_73, c_8003])).
% 16.62/7.12  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.62/7.12  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.62/7.12  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 16.62/7.12  tff(c_409, plain, (![A_91, B_92]: (u1_struct_0(g1_pre_topc(A_91, B_92))=A_91 | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))) | ~v1_pre_topc(g1_pre_topc(A_91, B_92)) | ~l1_pre_topc(g1_pre_topc(A_91, B_92)))), inference(reflexivity, [status(thm), theory('equality')], [c_244])).
% 16.62/7.12  tff(c_1938, plain, (![A_165]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_165), u1_pre_topc(A_165)))=u1_struct_0(A_165) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_165), u1_pre_topc(A_165))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_165), u1_pre_topc(A_165))) | ~l1_pre_topc(A_165))), inference(resolution, [status(thm)], [c_16, c_409])).
% 16.62/7.12  tff(c_1982, plain, (![A_166]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_166), u1_pre_topc(A_166)))=u1_struct_0(A_166) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_166), u1_pre_topc(A_166))) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_86, c_1938])).
% 16.62/7.12  tff(c_2089, plain, (![A_168]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168)))=u1_struct_0(A_168) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_73, c_1982])).
% 16.62/7.12  tff(c_52, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_77, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 16.62/7.12  tff(c_281, plain, (![D_72, A_73, B_74]: (v2_compts_1(D_72, A_73) | ~v2_compts_1(D_72, B_74) | ~m1_subset_1(D_72, k1_zfmisc_1(u1_struct_0(B_74))) | ~m1_subset_1(D_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_287, plain, (![A_73]: (v2_compts_1('#skF_3', A_73) | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc('#skF_1', A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_113, c_281])).
% 16.62/7.12  tff(c_293, plain, (![A_73]: (v2_compts_1('#skF_3', A_73) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc('#skF_1', A_73) | ~l1_pre_topc(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_287])).
% 16.62/7.12  tff(c_2904, plain, (![A_177]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177))) | ~l1_pre_topc(A_177))), inference(superposition, [status(thm), theory('equality')], [c_2089, c_293])).
% 16.62/7.12  tff(c_40, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_334, plain, (~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_40])).
% 16.62/7.12  tff(c_2907, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2904, c_334])).
% 16.62/7.12  tff(c_2949, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_113, c_2907])).
% 16.62/7.12  tff(c_2957, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2949])).
% 16.62/7.12  tff(c_2963, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_2957])).
% 16.62/7.12  tff(c_2969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2963])).
% 16.62/7.12  tff(c_2971, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2949])).
% 16.62/7.12  tff(c_251, plain, (![D_64, B_65, C_66, A_67]: (D_64=B_65 | g1_pre_topc(C_66, D_64)!=g1_pre_topc(A_67, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_253, plain, (![A_3, B_65, A_67]: (u1_pre_topc(A_3)=B_65 | g1_pre_topc(A_67, B_65)!=A_3 | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_67))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_251])).
% 16.62/7.12  tff(c_1134, plain, (![A_133, B_134]: (u1_pre_topc(g1_pre_topc(A_133, B_134))=B_134 | ~m1_subset_1(B_134, k1_zfmisc_1(k1_zfmisc_1(A_133))) | ~v1_pre_topc(g1_pre_topc(A_133, B_134)) | ~l1_pre_topc(g1_pre_topc(A_133, B_134)))), inference(reflexivity, [status(thm), theory('equality')], [c_253])).
% 16.62/7.12  tff(c_3381, plain, (![A_183]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183)))=u1_pre_topc(A_183) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183))) | ~l1_pre_topc(A_183))), inference(resolution, [status(thm)], [c_16, c_1134])).
% 16.62/7.12  tff(c_3434, plain, (![A_184]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_184), u1_pre_topc(A_184)))=u1_pre_topc(A_184) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_184), u1_pre_topc(A_184))) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_86, c_3381])).
% 16.62/7.12  tff(c_3440, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2971, c_3434])).
% 16.62/7.12  tff(c_3485, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3440])).
% 16.62/7.12  tff(c_2209, plain, (![A_168]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))) | ~l1_pre_topc(A_168))), inference(superposition, [status(thm), theory('equality')], [c_2089, c_86])).
% 16.62/7.12  tff(c_3524, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3485, c_2209])).
% 16.62/7.12  tff(c_3576, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2971, c_3524])).
% 16.62/7.12  tff(c_2215, plain, (![A_168]: (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_168)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))) | ~l1_pre_topc(A_168))), inference(superposition, [status(thm), theory('equality')], [c_2089, c_16])).
% 16.62/7.12  tff(c_3512, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3485, c_2215])).
% 16.62/7.12  tff(c_3568, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2971, c_3512])).
% 16.62/7.12  tff(c_275, plain, (![A_61, B_63]: (u1_struct_0(g1_pre_topc(A_61, B_63))=A_61 | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_61))) | ~v1_pre_topc(g1_pre_topc(A_61, B_63)) | ~l1_pre_topc(g1_pre_topc(A_61, B_63)))), inference(reflexivity, [status(thm), theory('equality')], [c_244])).
% 16.62/7.12  tff(c_3609, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_3568, c_275])).
% 16.62/7.12  tff(c_3621, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2971, c_3576, c_3609])).
% 16.62/7.12  tff(c_121, plain, (![A_52, B_53]: (m1_pre_topc(k1_pre_topc(A_52, B_53), A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.62/7.12  tff(c_130, plain, (![A_52]: (m1_pre_topc(k1_pre_topc(A_52, u1_struct_0(A_52)), A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_53, c_121])).
% 16.62/7.12  tff(c_132, plain, (![B_55, A_56]: (m1_pre_topc(B_55, A_56) | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.62/7.12  tff(c_140, plain, (![A_56]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56)), u1_struct_0(g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56)))), A_56) | ~l1_pre_topc(A_56) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56))))), inference(resolution, [status(thm)], [c_130, c_132])).
% 16.62/7.12  tff(c_3704, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), u1_struct_0('#skF_1')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3621, c_140])).
% 16.62/7.12  tff(c_3871, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), u1_struct_0('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2971, c_30, c_3704])).
% 16.62/7.12  tff(c_12, plain, (![A_6, B_7]: (m1_pre_topc(k1_pre_topc(A_6, B_7), A_6) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.62/7.12  tff(c_3791, plain, (![B_7]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_3621, c_12])).
% 16.62/7.12  tff(c_3929, plain, (![B_7]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2971, c_3791])).
% 16.62/7.12  tff(c_141, plain, (![A_57, B_58]: (u1_struct_0(k1_pre_topc(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.62/7.12  tff(c_152, plain, (![A_57]: (u1_struct_0(k1_pre_topc(A_57, u1_struct_0(A_57)))=u1_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_53, c_141])).
% 16.62/7.12  tff(c_378, plain, (![D_82, B_83, A_84]: (v2_compts_1(D_82, B_83) | ~v2_compts_1(D_82, A_84) | ~m1_subset_1(D_82, k1_zfmisc_1(u1_struct_0(B_83))) | ~m1_subset_1(D_82, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_5213, plain, (![D_204, A_205, A_206]: (v2_compts_1(D_204, k1_pre_topc(A_205, u1_struct_0(A_205))) | ~v2_compts_1(D_204, A_206) | ~m1_subset_1(D_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(D_204, k1_zfmisc_1(u1_struct_0(A_206))) | ~m1_pre_topc(k1_pre_topc(A_205, u1_struct_0(A_205)), A_206) | ~l1_pre_topc(A_206) | ~l1_pre_topc(A_205))), inference(superposition, [status(thm), theory('equality')], [c_152, c_378])).
% 16.62/7.12  tff(c_5245, plain, (![A_205]: (v2_compts_1('#skF_3', k1_pre_topc(A_205, u1_struct_0(A_205))) | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_pre_topc(k1_pre_topc(A_205, u1_struct_0(A_205)), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_113, c_5213])).
% 16.62/7.12  tff(c_5255, plain, (![A_205]: (v2_compts_1('#skF_3', k1_pre_topc(A_205, u1_struct_0(A_205))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_pre_topc(k1_pre_topc(A_205, u1_struct_0(A_205)), '#skF_1') | ~l1_pre_topc(A_205))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_77, c_5245])).
% 16.62/7.12  tff(c_5754, plain, (![D_214, A_215, A_216]: (v2_compts_1(D_214, A_215) | ~v2_compts_1(D_214, k1_pre_topc(A_216, u1_struct_0(A_216))) | ~m1_subset_1(D_214, k1_zfmisc_1(u1_struct_0(A_216))) | ~m1_subset_1(D_214, k1_zfmisc_1(u1_struct_0(A_215))) | ~m1_pre_topc(k1_pre_topc(A_216, u1_struct_0(A_216)), A_215) | ~l1_pre_topc(A_215) | ~l1_pre_topc(A_216))), inference(superposition, [status(thm), theory('equality')], [c_152, c_281])).
% 16.62/7.12  tff(c_5826, plain, (![A_217, A_218]: (v2_compts_1('#skF_3', A_217) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_217))) | ~m1_pre_topc(k1_pre_topc(A_218, u1_struct_0(A_218)), A_217) | ~l1_pre_topc(A_217) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_pre_topc(k1_pre_topc(A_218, u1_struct_0(A_218)), '#skF_1') | ~l1_pre_topc(A_218))), inference(resolution, [status(thm)], [c_5255, c_5754])).
% 16.62/7.12  tff(c_5832, plain, (![A_218]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(k1_pre_topc(A_218, u1_struct_0(A_218)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_pre_topc(k1_pre_topc(A_218, u1_struct_0(A_218)), '#skF_1') | ~l1_pre_topc(A_218))), inference(superposition, [status(thm), theory('equality')], [c_3621, c_5826])).
% 16.62/7.12  tff(c_5862, plain, (![A_218]: (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(k1_pre_topc(A_218, u1_struct_0(A_218)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_pre_topc(k1_pre_topc(A_218, u1_struct_0(A_218)), '#skF_1') | ~l1_pre_topc(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_2971, c_113, c_5832])).
% 16.62/7.12  tff(c_6182, plain, (![A_228]: (~m1_pre_topc(k1_pre_topc(A_228, u1_struct_0(A_228)), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_pre_topc(k1_pre_topc(A_228, u1_struct_0(A_228)), '#skF_1') | ~l1_pre_topc(A_228))), inference(negUnitSimplification, [status(thm)], [c_334, c_5862])).
% 16.62/7.12  tff(c_6186, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), '#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_3929, c_6182])).
% 16.62/7.12  tff(c_6246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_3621, c_2971, c_3871, c_3621, c_113, c_3621, c_6186])).
% 16.62/7.12  tff(c_6247, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_40])).
% 16.62/7.12  tff(c_6254, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_6247])).
% 16.62/7.12  tff(c_8139, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8047, c_6254])).
% 16.62/7.12  tff(c_8231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_113, c_8139])).
% 16.62/7.12  tff(c_8233, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_6247])).
% 16.62/7.12  tff(c_6248, plain, (v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_40])).
% 16.62/7.12  tff(c_36, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_8240, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_6248, c_36])).
% 16.62/7.12  tff(c_8241, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_8240])).
% 16.62/7.12  tff(c_8270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8233, c_8241])).
% 16.62/7.12  tff(c_8271, plain, (~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8240])).
% 16.62/7.12  tff(c_8274, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_8271])).
% 16.62/7.12  tff(c_8272, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_8240])).
% 16.62/7.12  tff(c_14, plain, (![A_6, B_7]: (v1_pre_topc(k1_pre_topc(A_6, B_7)) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.62/7.12  tff(c_8298, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_8272, c_14])).
% 16.62/7.12  tff(c_8326, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_8298])).
% 16.62/7.12  tff(c_8332, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_8326])).
% 16.62/7.12  tff(c_8338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_8332])).
% 16.62/7.12  tff(c_8340, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_8298])).
% 16.62/7.12  tff(c_8663, plain, (![A_333, B_334]: (u1_pre_topc(g1_pre_topc(A_333, B_334))=B_334 | ~m1_subset_1(B_334, k1_zfmisc_1(k1_zfmisc_1(A_333))) | ~v1_pre_topc(g1_pre_topc(A_333, B_334)) | ~l1_pre_topc(g1_pre_topc(A_333, B_334)))), inference(reflexivity, [status(thm), theory('equality')], [c_253])).
% 16.62/7.12  tff(c_10242, plain, (![A_400]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_400), u1_pre_topc(A_400)))=u1_pre_topc(A_400) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_400), u1_pre_topc(A_400))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_400), u1_pre_topc(A_400))) | ~l1_pre_topc(A_400))), inference(resolution, [status(thm)], [c_16, c_8663])).
% 16.62/7.12  tff(c_10294, plain, (![A_401]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401)))=u1_pre_topc(A_401) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401))) | ~l1_pre_topc(A_401))), inference(resolution, [status(thm)], [c_86, c_10242])).
% 16.62/7.12  tff(c_10327, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8340, c_10294])).
% 16.62/7.12  tff(c_10349, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10327])).
% 16.62/7.12  tff(c_10418, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10349, c_16])).
% 16.62/7.12  tff(c_10439, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_8340, c_10418])).
% 16.62/7.12  tff(c_10409, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10349, c_6])).
% 16.62/7.12  tff(c_10433, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8340, c_10409])).
% 16.62/7.12  tff(c_11404, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_10433])).
% 16.62/7.12  tff(c_11410, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86, c_11404])).
% 16.62/7.12  tff(c_11416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_11410])).
% 16.62/7.12  tff(c_11417, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_10433])).
% 16.62/7.12  tff(c_20, plain, (![C_13, A_9, D_14, B_10]: (C_13=A_9 | g1_pre_topc(C_13, D_14)!=g1_pre_topc(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_11462, plain, (![C_13, D_14]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=C_13 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_13, D_14) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))))), inference(superposition, [status(thm), theory('equality')], [c_11417, c_20])).
% 16.62/7.12  tff(c_11479, plain, (![C_13, D_14]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=C_13 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_10439, c_11462])).
% 16.62/7.12  tff(c_11657, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_11479])).
% 16.62/7.12  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_compts_1('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_8302, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_6248, c_8272, c_38])).
% 16.62/7.12  tff(c_11676, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_8302])).
% 16.62/7.12  tff(c_11679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8274, c_11676])).
% 16.62/7.12  tff(c_11680, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_8271])).
% 16.62/7.12  tff(c_11681, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8271])).
% 16.62/7.12  tff(c_11683, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_6248, c_38])).
% 16.62/7.12  tff(c_11684, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_11683])).
% 16.62/7.12  tff(c_11793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8233, c_11684])).
% 16.62/7.12  tff(c_11795, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_11683])).
% 16.62/7.12  tff(c_11819, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_11795, c_14])).
% 16.62/7.12  tff(c_11925, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_11819])).
% 16.62/7.12  tff(c_11931, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_11925])).
% 16.62/7.12  tff(c_11937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_11931])).
% 16.62/7.12  tff(c_11939, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_11819])).
% 16.62/7.12  tff(c_12323, plain, (![A_433, B_434]: (u1_struct_0(g1_pre_topc(A_433, B_434))=A_433 | ~m1_subset_1(B_434, k1_zfmisc_1(k1_zfmisc_1(A_433))) | ~v1_pre_topc(g1_pre_topc(A_433, B_434)) | ~l1_pre_topc(g1_pre_topc(A_433, B_434)))), inference(reflexivity, [status(thm), theory('equality')], [c_244])).
% 16.62/7.12  tff(c_14277, plain, (![A_508]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_508), u1_pre_topc(A_508)))=u1_struct_0(A_508) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_508), u1_pre_topc(A_508))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_508), u1_pre_topc(A_508))) | ~l1_pre_topc(A_508))), inference(resolution, [status(thm)], [c_16, c_12323])).
% 16.62/7.12  tff(c_14333, plain, (![A_509]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_509), u1_pre_topc(A_509)))=u1_struct_0(A_509) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_509), u1_pre_topc(A_509))) | ~l1_pre_topc(A_509))), inference(resolution, [status(thm)], [c_86, c_14277])).
% 16.62/7.12  tff(c_14366, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_11939, c_14333])).
% 16.62/7.12  tff(c_14391, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14366])).
% 16.62/7.12  tff(c_14511, plain, (![B_7]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_14391, c_12])).
% 16.62/7.12  tff(c_16494, plain, (![B_526]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_526), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_526, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_11939, c_14511])).
% 16.62/7.12  tff(c_24, plain, (![B_20, A_18]: (m1_pre_topc(B_20, A_18) | ~m1_pre_topc(B_20, g1_pre_topc(u1_struct_0(A_18), u1_pre_topc(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.62/7.12  tff(c_16497, plain, (![B_526]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_526), '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_526, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_16494, c_24])).
% 16.62/7.12  tff(c_16506, plain, (![B_526]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_526), '#skF_1') | ~m1_subset_1(B_526, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16497])).
% 16.62/7.12  tff(c_8232, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_6247])).
% 16.62/7.12  tff(c_14606, plain, (![B_7]: (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_11939, c_14511])).
% 16.62/7.12  tff(c_11794, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_11683])).
% 16.62/7.12  tff(c_22, plain, (![A_15, B_17]: (u1_struct_0(k1_pre_topc(A_15, B_17))=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.62/7.12  tff(c_11920, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_11794, c_22])).
% 16.62/7.12  tff(c_12090, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11939, c_11920])).
% 16.62/7.12  tff(c_12729, plain, (![B_447, A_448]: (v2_compts_1(u1_struct_0(B_447), A_448) | ~v2_compts_1(u1_struct_0(B_447), B_447) | ~m1_subset_1(u1_struct_0(B_447), k1_zfmisc_1(u1_struct_0(A_448))) | ~m1_pre_topc(B_447, A_448) | ~l1_pre_topc(A_448))), inference(resolution, [status(thm)], [c_53, c_281])).
% 16.62/7.12  tff(c_12737, plain, (![A_448]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_448) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_448))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_448) | ~l1_pre_topc(A_448))), inference(superposition, [status(thm), theory('equality')], [c_12090, c_12729])).
% 16.62/7.12  tff(c_12749, plain, (![A_448]: (v2_compts_1('#skF_2', A_448) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_448))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_448) | ~l1_pre_topc(A_448))), inference(demodulation, [status(thm), theory('equality')], [c_12090, c_12090, c_12737])).
% 16.62/7.12  tff(c_21297, plain, (~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitLeft, [status(thm)], [c_12749])).
% 16.62/7.12  tff(c_11951, plain, (![D_419, B_420, A_421]: (v2_compts_1(D_419, B_420) | ~v2_compts_1(D_419, A_421) | ~m1_subset_1(D_419, k1_zfmisc_1(u1_struct_0(B_420))) | ~m1_subset_1(D_419, k1_zfmisc_1(u1_struct_0(A_421))) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_12456, plain, (![B_436, A_437]: (v2_compts_1(u1_struct_0(B_436), B_436) | ~v2_compts_1(u1_struct_0(B_436), A_437) | ~m1_subset_1(u1_struct_0(B_436), k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437))), inference(resolution, [status(thm)], [c_53, c_11951])).
% 16.62/7.12  tff(c_12462, plain, (![A_437]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_437) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_437) | ~l1_pre_topc(A_437))), inference(superposition, [status(thm), theory('equality')], [c_12090, c_12456])).
% 16.62/7.12  tff(c_12487, plain, (![A_437]: (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', A_437) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_437) | ~l1_pre_topc(A_437))), inference(demodulation, [status(thm), theory('equality')], [c_12090, c_12090, c_12462])).
% 16.62/7.12  tff(c_21928, plain, (![A_605]: (~v2_compts_1('#skF_2', A_605) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_605))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_605) | ~l1_pre_topc(A_605))), inference(negUnitSimplification, [status(thm)], [c_21297, c_12487])).
% 16.62/7.12  tff(c_21936, plain, (~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14606, c_21928])).
% 16.62/7.12  tff(c_21952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11681, c_11939, c_11681, c_14391, c_8232, c_21936])).
% 16.62/7.12  tff(c_21961, plain, (![A_606]: (v2_compts_1('#skF_2', A_606) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_606))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_606) | ~l1_pre_topc(A_606))), inference(splitRight, [status(thm)], [c_12749])).
% 16.62/7.12  tff(c_21965, plain, (v2_compts_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16506, c_21961])).
% 16.62/7.12  tff(c_21981, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11681, c_30, c_21965])).
% 16.62/7.12  tff(c_21983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11680, c_21981])).
% 16.62/7.12  tff(c_21985, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_46])).
% 16.62/7.12  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_22067, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_21985, c_42])).
% 16.62/7.12  tff(c_22068, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22067])).
% 16.62/7.12  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_22078, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_21985, c_44])).
% 16.62/7.12  tff(c_22092, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_22078, c_14])).
% 16.62/7.12  tff(c_22095, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_22092])).
% 16.62/7.12  tff(c_22101, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_22095])).
% 16.62/7.12  tff(c_22107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_22101])).
% 16.62/7.12  tff(c_22109, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_22092])).
% 16.62/7.12  tff(c_22073, plain, (![C_619, A_620, D_621, B_622]: (C_619=A_620 | g1_pre_topc(C_619, D_621)!=g1_pre_topc(A_620, B_622) | ~m1_subset_1(B_622, k1_zfmisc_1(k1_zfmisc_1(A_620))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_22075, plain, (![A_3, A_620, B_622]: (u1_struct_0(A_3)=A_620 | g1_pre_topc(A_620, B_622)!=A_3 | ~m1_subset_1(B_622, k1_zfmisc_1(k1_zfmisc_1(A_620))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_22073])).
% 16.62/7.12  tff(c_22304, plain, (![A_646, B_647]: (u1_struct_0(g1_pre_topc(A_646, B_647))=A_646 | ~m1_subset_1(B_647, k1_zfmisc_1(k1_zfmisc_1(A_646))) | ~v1_pre_topc(g1_pre_topc(A_646, B_647)) | ~l1_pre_topc(g1_pre_topc(A_646, B_647)))), inference(reflexivity, [status(thm), theory('equality')], [c_22075])).
% 16.62/7.12  tff(c_23766, plain, (![A_708]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_708), u1_pre_topc(A_708)))=u1_struct_0(A_708) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_708), u1_pre_topc(A_708))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_708), u1_pre_topc(A_708))) | ~l1_pre_topc(A_708))), inference(resolution, [status(thm)], [c_16, c_22304])).
% 16.62/7.12  tff(c_23810, plain, (![A_709]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_709), u1_pre_topc(A_709)))=u1_struct_0(A_709) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_709), u1_pre_topc(A_709))) | ~l1_pre_topc(A_709))), inference(resolution, [status(thm)], [c_86, c_23766])).
% 16.62/7.12  tff(c_23840, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22109, c_23810])).
% 16.62/7.12  tff(c_23858, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_23840])).
% 16.62/7.12  tff(c_23860, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23858, c_22078])).
% 16.62/7.12  tff(c_22090, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_22078, c_12])).
% 16.62/7.12  tff(c_22529, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22109, c_22090])).
% 16.62/7.12  tff(c_22532, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22529, c_24])).
% 16.62/7.12  tff(c_22541, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22532])).
% 16.62/7.12  tff(c_21984, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_46])).
% 16.62/7.12  tff(c_22091, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_22078, c_22])).
% 16.62/7.12  tff(c_22133, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22109, c_22091])).
% 16.62/7.12  tff(c_22244, plain, (![D_635, B_636, A_637]: (v2_compts_1(D_635, B_636) | ~v2_compts_1(D_635, A_637) | ~m1_subset_1(D_635, k1_zfmisc_1(u1_struct_0(B_636))) | ~m1_subset_1(D_635, k1_zfmisc_1(u1_struct_0(A_637))) | ~m1_pre_topc(B_636, A_637) | ~l1_pre_topc(A_637))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_22837, plain, (![B_669, A_670]: (v2_compts_1(u1_struct_0(B_669), B_669) | ~v2_compts_1(u1_struct_0(B_669), A_670) | ~m1_subset_1(u1_struct_0(B_669), k1_zfmisc_1(u1_struct_0(A_670))) | ~m1_pre_topc(B_669, A_670) | ~l1_pre_topc(A_670))), inference(resolution, [status(thm)], [c_53, c_22244])).
% 16.62/7.12  tff(c_22851, plain, (![A_670]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_670) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_670))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_670) | ~l1_pre_topc(A_670))), inference(superposition, [status(thm), theory('equality')], [c_22133, c_22837])).
% 16.62/7.12  tff(c_22865, plain, (![A_670]: (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', A_670) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_670))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_670) | ~l1_pre_topc(A_670))), inference(demodulation, [status(thm), theory('equality')], [c_22133, c_22133, c_22851])).
% 16.62/7.12  tff(c_26149, plain, (![A_736]: (~v2_compts_1('#skF_2', A_736) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_736))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_736) | ~l1_pre_topc(A_736))), inference(splitLeft, [status(thm)], [c_22865])).
% 16.62/7.12  tff(c_26155, plain, (~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_22529, c_26149])).
% 16.62/7.12  tff(c_26165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22109, c_23860, c_23858, c_21984, c_26155])).
% 16.62/7.12  tff(c_26166, plain, (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_22865])).
% 16.62/7.12  tff(c_22110, plain, (![D_623, A_624, B_625]: (v2_compts_1(D_623, A_624) | ~v2_compts_1(D_623, B_625) | ~m1_subset_1(D_623, k1_zfmisc_1(u1_struct_0(B_625))) | ~m1_subset_1(D_623, k1_zfmisc_1(u1_struct_0(A_624))) | ~m1_pre_topc(B_625, A_624) | ~l1_pre_topc(A_624))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_22701, plain, (![B_658, A_659]: (v2_compts_1(u1_struct_0(B_658), A_659) | ~v2_compts_1(u1_struct_0(B_658), B_658) | ~m1_subset_1(u1_struct_0(B_658), k1_zfmisc_1(u1_struct_0(A_659))) | ~m1_pre_topc(B_658, A_659) | ~l1_pre_topc(A_659))), inference(resolution, [status(thm)], [c_53, c_22110])).
% 16.62/7.12  tff(c_22707, plain, (![A_659]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_659) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_659))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_659) | ~l1_pre_topc(A_659))), inference(superposition, [status(thm), theory('equality')], [c_22133, c_22701])).
% 16.62/7.12  tff(c_22712, plain, (![A_659]: (v2_compts_1('#skF_2', A_659) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_659))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_659) | ~l1_pre_topc(A_659))), inference(demodulation, [status(thm), theory('equality')], [c_22133, c_22133, c_22707])).
% 16.62/7.12  tff(c_26179, plain, (![A_740]: (v2_compts_1('#skF_2', A_740) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_740))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_740) | ~l1_pre_topc(A_740))), inference(demodulation, [status(thm), theory('equality')], [c_26166, c_22712])).
% 16.62/7.12  tff(c_26182, plain, (v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22541, c_26179])).
% 16.62/7.12  tff(c_26191, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_23860, c_26182])).
% 16.62/7.12  tff(c_26193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22068, c_26191])).
% 16.62/7.12  tff(c_26194, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_22067])).
% 16.62/7.12  tff(c_26205, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_21985, c_44])).
% 16.62/7.12  tff(c_26219, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_26205, c_14])).
% 16.62/7.12  tff(c_26223, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_26219])).
% 16.62/7.12  tff(c_26229, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_26223])).
% 16.62/7.12  tff(c_26235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26229])).
% 16.62/7.12  tff(c_26237, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_26219])).
% 16.62/7.12  tff(c_22062, plain, (![D_615, B_616, C_617, A_618]: (D_615=B_616 | g1_pre_topc(C_617, D_615)!=g1_pre_topc(A_618, B_616) | ~m1_subset_1(B_616, k1_zfmisc_1(k1_zfmisc_1(A_618))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_22064, plain, (![A_3, B_616, A_618]: (u1_pre_topc(A_3)=B_616 | g1_pre_topc(A_618, B_616)!=A_3 | ~m1_subset_1(B_616, k1_zfmisc_1(k1_zfmisc_1(A_618))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_22062])).
% 16.62/7.12  tff(c_26430, plain, (![A_768, B_769]: (u1_pre_topc(g1_pre_topc(A_768, B_769))=B_769 | ~m1_subset_1(B_769, k1_zfmisc_1(k1_zfmisc_1(A_768))) | ~v1_pre_topc(g1_pre_topc(A_768, B_769)) | ~l1_pre_topc(g1_pre_topc(A_768, B_769)))), inference(reflexivity, [status(thm), theory('equality')], [c_22064])).
% 16.62/7.12  tff(c_27685, plain, (![A_827]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_827), u1_pre_topc(A_827)))=u1_pre_topc(A_827) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_827), u1_pre_topc(A_827))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_827), u1_pre_topc(A_827))) | ~l1_pre_topc(A_827))), inference(resolution, [status(thm)], [c_16, c_26430])).
% 16.62/7.12  tff(c_27729, plain, (![A_828]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_828), u1_pre_topc(A_828)))=u1_pre_topc(A_828) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_828), u1_pre_topc(A_828))) | ~l1_pre_topc(A_828))), inference(resolution, [status(thm)], [c_86, c_27685])).
% 16.62/7.12  tff(c_27759, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26237, c_27729])).
% 16.62/7.12  tff(c_27777, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_27759])).
% 16.62/7.12  tff(c_27803, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_27777, c_16])).
% 16.62/7.12  tff(c_27824, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_26237, c_27803])).
% 16.62/7.12  tff(c_27794, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_27777, c_6])).
% 16.62/7.12  tff(c_27818, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26237, c_27794])).
% 16.62/7.12  tff(c_28648, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_27818])).
% 16.62/7.12  tff(c_28654, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86, c_28648])).
% 16.62/7.12  tff(c_28660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28654])).
% 16.62/7.12  tff(c_28661, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_27818])).
% 16.62/7.12  tff(c_28786, plain, (![C_13, D_14]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=C_13 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_13, D_14) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))))), inference(superposition, [status(thm), theory('equality')], [c_28661, c_20])).
% 16.62/7.12  tff(c_28807, plain, (![C_13, D_14]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=C_13 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_27824, c_28786])).
% 16.62/7.12  tff(c_28854, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_28807])).
% 16.62/7.12  tff(c_28871, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28854, c_26205])).
% 16.62/7.12  tff(c_28873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26194, c_28871])).
% 16.62/7.12  tff(c_28875, plain, (~v2_compts_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 16.62/7.12  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1') | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_28887, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_compts_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_28875, c_48])).
% 16.62/7.12  tff(c_28888, plain, (~v2_compts_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28887])).
% 16.62/7.12  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.62/7.12  tff(c_28984, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_28875, c_50])).
% 16.62/7.12  tff(c_28998, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28984, c_14])).
% 16.62/7.12  tff(c_29020, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_28998])).
% 16.62/7.12  tff(c_29026, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_29020])).
% 16.62/7.12  tff(c_29032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_29026])).
% 16.62/7.12  tff(c_29034, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_28998])).
% 16.62/7.12  tff(c_28876, plain, (![A_847, B_848]: (v1_pre_topc(g1_pre_topc(A_847, B_848)) | ~m1_subset_1(B_848, k1_zfmisc_1(k1_zfmisc_1(A_847))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.62/7.12  tff(c_28884, plain, (![A_8]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_8), u1_pre_topc(A_8))) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_16, c_28876])).
% 16.62/7.12  tff(c_29014, plain, (![D_867, B_868, C_869, A_870]: (D_867=B_868 | g1_pre_topc(C_869, D_867)!=g1_pre_topc(A_870, B_868) | ~m1_subset_1(B_868, k1_zfmisc_1(k1_zfmisc_1(A_870))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_29016, plain, (![A_3, B_868, A_870]: (u1_pre_topc(A_3)=B_868 | g1_pre_topc(A_870, B_868)!=A_3 | ~m1_subset_1(B_868, k1_zfmisc_1(k1_zfmisc_1(A_870))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_29014])).
% 16.62/7.12  tff(c_29860, plain, (![A_931, B_932]: (u1_pre_topc(g1_pre_topc(A_931, B_932))=B_932 | ~m1_subset_1(B_932, k1_zfmisc_1(k1_zfmisc_1(A_931))) | ~v1_pre_topc(g1_pre_topc(A_931, B_932)) | ~l1_pre_topc(g1_pre_topc(A_931, B_932)))), inference(reflexivity, [status(thm), theory('equality')], [c_29016])).
% 16.62/7.12  tff(c_30611, plain, (![A_955]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_955), u1_pre_topc(A_955)))=u1_pre_topc(A_955) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_955), u1_pre_topc(A_955))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_955), u1_pre_topc(A_955))) | ~l1_pre_topc(A_955))), inference(resolution, [status(thm)], [c_16, c_29860])).
% 16.62/7.12  tff(c_30655, plain, (![A_956]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_956), u1_pre_topc(A_956)))=u1_pre_topc(A_956) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_956), u1_pre_topc(A_956))) | ~l1_pre_topc(A_956))), inference(resolution, [status(thm)], [c_28884, c_30611])).
% 16.62/7.12  tff(c_30685, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_29034, c_30655])).
% 16.62/7.12  tff(c_30703, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30685])).
% 16.62/7.12  tff(c_30723, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_30703, c_6])).
% 16.62/7.12  tff(c_30749, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_29034, c_30723])).
% 16.62/7.12  tff(c_31733, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_30749])).
% 16.62/7.12  tff(c_31739, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28884, c_31733])).
% 16.62/7.12  tff(c_31745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_31739])).
% 16.62/7.12  tff(c_31747, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_30749])).
% 16.62/7.12  tff(c_29005, plain, (![C_863, A_864, D_865, B_866]: (C_863=A_864 | g1_pre_topc(C_863, D_865)!=g1_pre_topc(A_864, B_866) | ~m1_subset_1(B_866, k1_zfmisc_1(k1_zfmisc_1(A_864))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_29009, plain, (![A_3, C_863, D_865]: (u1_struct_0(A_3)=C_863 | g1_pre_topc(C_863, D_865)!=A_3 | ~m1_subset_1(u1_pre_topc(A_3), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3)))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_29005])).
% 16.62/7.12  tff(c_31748, plain, (![C_970, D_971]: (u1_struct_0(g1_pre_topc(C_970, D_971))=C_970 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_970, D_971)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_970, D_971))))) | ~v1_pre_topc(g1_pre_topc(C_970, D_971)) | ~l1_pre_topc(g1_pre_topc(C_970, D_971)))), inference(reflexivity, [status(thm), theory('equality')], [c_29009])).
% 16.62/7.12  tff(c_31799, plain, (![C_972, D_973]: (u1_struct_0(g1_pre_topc(C_972, D_973))=C_972 | ~v1_pre_topc(g1_pre_topc(C_972, D_973)) | ~l1_pre_topc(g1_pre_topc(C_972, D_973)))), inference(resolution, [status(thm)], [c_16, c_31748])).
% 16.62/7.12  tff(c_31802, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_31747, c_31799])).
% 16.62/7.12  tff(c_31829, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29034, c_31802])).
% 16.62/7.12  tff(c_31848, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_31829, c_28984])).
% 16.62/7.12  tff(c_28996, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28984, c_12])).
% 16.62/7.12  tff(c_29616, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_29034, c_28996])).
% 16.62/7.12  tff(c_29619, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_29616, c_24])).
% 16.62/7.12  tff(c_29628, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_29619])).
% 16.62/7.12  tff(c_28874, plain, (v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_52])).
% 16.62/7.12  tff(c_28997, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28984, c_22])).
% 16.62/7.12  tff(c_29047, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_29034, c_28997])).
% 16.62/7.12  tff(c_29116, plain, (![D_875, B_876, A_877]: (v2_compts_1(D_875, B_876) | ~v2_compts_1(D_875, A_877) | ~m1_subset_1(D_875, k1_zfmisc_1(u1_struct_0(B_876))) | ~m1_subset_1(D_875, k1_zfmisc_1(u1_struct_0(A_877))) | ~m1_pre_topc(B_876, A_877) | ~l1_pre_topc(A_877))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_29824, plain, (![B_926, A_927]: (v2_compts_1(u1_struct_0(B_926), B_926) | ~v2_compts_1(u1_struct_0(B_926), A_927) | ~m1_subset_1(u1_struct_0(B_926), k1_zfmisc_1(u1_struct_0(A_927))) | ~m1_pre_topc(B_926, A_927) | ~l1_pre_topc(A_927))), inference(resolution, [status(thm)], [c_53, c_29116])).
% 16.62/7.12  tff(c_29838, plain, (![A_927]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_927) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_927))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_927) | ~l1_pre_topc(A_927))), inference(superposition, [status(thm), theory('equality')], [c_29047, c_29824])).
% 16.62/7.12  tff(c_29852, plain, (![A_927]: (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~v2_compts_1('#skF_2', A_927) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_927))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_927) | ~l1_pre_topc(A_927))), inference(demodulation, [status(thm), theory('equality')], [c_29047, c_29047, c_29838])).
% 16.62/7.12  tff(c_32913, plain, (![A_980]: (~v2_compts_1('#skF_2', A_980) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_980))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_980) | ~l1_pre_topc(A_980))), inference(splitLeft, [status(thm)], [c_29852])).
% 16.62/7.12  tff(c_32919, plain, (~v2_compts_1('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_29616, c_32913])).
% 16.62/7.12  tff(c_32929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29034, c_31848, c_31829, c_28874, c_32919])).
% 16.62/7.12  tff(c_32930, plain, (v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'))), inference(splitRight, [status(thm)], [c_29852])).
% 16.62/7.12  tff(c_29330, plain, (![D_893, A_894, B_895]: (v2_compts_1(D_893, A_894) | ~v2_compts_1(D_893, B_895) | ~m1_subset_1(D_893, k1_zfmisc_1(u1_struct_0(B_895))) | ~m1_subset_1(D_893, k1_zfmisc_1(u1_struct_0(A_894))) | ~m1_pre_topc(B_895, A_894) | ~l1_pre_topc(A_894))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.62/7.12  tff(c_29735, plain, (![B_913, A_914]: (v2_compts_1(u1_struct_0(B_913), A_914) | ~v2_compts_1(u1_struct_0(B_913), B_913) | ~m1_subset_1(u1_struct_0(B_913), k1_zfmisc_1(u1_struct_0(A_914))) | ~m1_pre_topc(B_913, A_914) | ~l1_pre_topc(A_914))), inference(resolution, [status(thm)], [c_53, c_29330])).
% 16.62/7.12  tff(c_29743, plain, (![A_914]: (v2_compts_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), A_914) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_914))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_914) | ~l1_pre_topc(A_914))), inference(superposition, [status(thm), theory('equality')], [c_29047, c_29735])).
% 16.62/7.12  tff(c_29748, plain, (![A_914]: (v2_compts_1('#skF_2', A_914) | ~v2_compts_1('#skF_2', k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_914))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_914) | ~l1_pre_topc(A_914))), inference(demodulation, [status(thm), theory('equality')], [c_29047, c_29047, c_29743])).
% 16.62/7.12  tff(c_33143, plain, (![A_983]: (v2_compts_1('#skF_2', A_983) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_983))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2'), A_983) | ~l1_pre_topc(A_983))), inference(demodulation, [status(thm), theory('equality')], [c_32930, c_29748])).
% 16.62/7.12  tff(c_33146, plain, (v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_29628, c_33143])).
% 16.62/7.12  tff(c_33155, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_31848, c_33146])).
% 16.62/7.12  tff(c_33157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28888, c_33155])).
% 16.62/7.12  tff(c_33158, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_28887])).
% 16.62/7.12  tff(c_33254, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_28875, c_50])).
% 16.62/7.12  tff(c_33268, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_33254, c_14])).
% 16.62/7.12  tff(c_33293, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_33268])).
% 16.62/7.12  tff(c_33310, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_73, c_33293])).
% 16.62/7.12  tff(c_33316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_33310])).
% 16.62/7.12  tff(c_33318, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_33268])).
% 16.62/7.12  tff(c_33287, plain, (![D_1001, B_1002, C_1003, A_1004]: (D_1001=B_1002 | g1_pre_topc(C_1003, D_1001)!=g1_pre_topc(A_1004, B_1002) | ~m1_subset_1(B_1002, k1_zfmisc_1(k1_zfmisc_1(A_1004))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_33289, plain, (![A_3, B_1002, A_1004]: (u1_pre_topc(A_3)=B_1002 | g1_pre_topc(A_1004, B_1002)!=A_3 | ~m1_subset_1(B_1002, k1_zfmisc_1(k1_zfmisc_1(A_1004))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33287])).
% 16.62/7.12  tff(c_33501, plain, (![A_1027, B_1028]: (u1_pre_topc(g1_pre_topc(A_1027, B_1028))=B_1028 | ~m1_subset_1(B_1028, k1_zfmisc_1(k1_zfmisc_1(A_1027))) | ~v1_pre_topc(g1_pre_topc(A_1027, B_1028)) | ~l1_pre_topc(g1_pre_topc(A_1027, B_1028)))), inference(reflexivity, [status(thm), theory('equality')], [c_33289])).
% 16.62/7.12  tff(c_34895, plain, (![A_1092]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1092), u1_pre_topc(A_1092)))=u1_pre_topc(A_1092) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1092), u1_pre_topc(A_1092))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1092), u1_pre_topc(A_1092))) | ~l1_pre_topc(A_1092))), inference(resolution, [status(thm)], [c_16, c_33501])).
% 16.62/7.12  tff(c_35002, plain, (![A_1095]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1095), u1_pre_topc(A_1095)))=u1_pre_topc(A_1095) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1095), u1_pre_topc(A_1095))) | ~l1_pre_topc(A_1095))), inference(resolution, [status(thm)], [c_28884, c_34895])).
% 16.62/7.12  tff(c_35032, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33318, c_35002])).
% 16.62/7.12  tff(c_35050, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_35032])).
% 16.62/7.12  tff(c_35082, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35050, c_16])).
% 16.62/7.12  tff(c_35107, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_33318, c_35082])).
% 16.62/7.12  tff(c_33278, plain, (![C_997, A_998, D_999, B_1000]: (C_997=A_998 | g1_pre_topc(C_997, D_999)!=g1_pre_topc(A_998, B_1000) | ~m1_subset_1(B_1000, k1_zfmisc_1(k1_zfmisc_1(A_998))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.62/7.12  tff(c_33282, plain, (![A_3, C_997, D_999]: (u1_struct_0(A_3)=C_997 | g1_pre_topc(C_997, D_999)!=A_3 | ~m1_subset_1(u1_pre_topc(A_3), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3)))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33278])).
% 16.62/7.12  tff(c_35705, plain, (![C_1099, D_1100]: (u1_struct_0(g1_pre_topc(C_1099, D_1100))=C_1099 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_1099, D_1100)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_1099, D_1100))))) | ~v1_pre_topc(g1_pre_topc(C_1099, D_1100)) | ~l1_pre_topc(g1_pre_topc(C_1099, D_1100)))), inference(reflexivity, [status(thm), theory('equality')], [c_33282])).
% 16.62/7.12  tff(c_35717, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35050, c_35705])).
% 16.62/7.12  tff(c_35738, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_33318, c_35107, c_35717])).
% 16.62/7.12  tff(c_35776, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_35738])).
% 16.62/7.12  tff(c_35782, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28884, c_35776])).
% 16.62/7.12  tff(c_35788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_35782])).
% 16.62/7.12  tff(c_35789, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_35738])).
% 16.62/7.12  tff(c_35809, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_35789, c_33254])).
% 16.62/7.12  tff(c_35814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33158, c_35809])).
% 16.62/7.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.62/7.12  
% 16.62/7.12  Inference rules
% 16.62/7.12  ----------------------
% 16.62/7.12  #Ref     : 85
% 16.62/7.12  #Sup     : 9391
% 16.62/7.12  #Fact    : 0
% 16.62/7.12  #Define  : 0
% 16.62/7.12  #Split   : 50
% 16.62/7.12  #Chain   : 0
% 16.62/7.12  #Close   : 0
% 16.62/7.12  
% 16.62/7.12  Ordering : KBO
% 16.62/7.12  
% 16.62/7.12  Simplification rules
% 16.62/7.12  ----------------------
% 16.62/7.12  #Subsume      : 1544
% 16.62/7.12  #Demod        : 11530
% 16.62/7.12  #Tautology    : 1481
% 16.62/7.12  #SimpNegUnit  : 42
% 16.62/7.12  #BackRed      : 109
% 16.62/7.12  
% 16.62/7.12  #Partial instantiations: 0
% 16.62/7.12  #Strategies tried      : 1
% 16.62/7.12  
% 16.62/7.12  Timing (in seconds)
% 16.62/7.12  ----------------------
% 16.62/7.12  Preprocessing        : 0.33
% 16.62/7.12  Parsing              : 0.18
% 16.62/7.12  CNF conversion       : 0.03
% 16.62/7.12  Main loop            : 5.94
% 16.62/7.12  Inferencing          : 1.38
% 16.62/7.12  Reduction            : 2.56
% 16.62/7.12  Demodulation         : 2.03
% 16.62/7.12  BG Simplification    : 0.21
% 16.62/7.12  Subsumption          : 1.45
% 16.62/7.12  Abstraction          : 0.29
% 16.62/7.12  MUC search           : 0.00
% 16.62/7.12  Cooper               : 0.00
% 16.62/7.12  Total                : 6.37
% 16.62/7.12  Index Insertion      : 0.00
% 16.62/7.12  Index Deletion       : 0.00
% 16.62/7.12  Index Matching       : 0.00
% 16.62/7.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
