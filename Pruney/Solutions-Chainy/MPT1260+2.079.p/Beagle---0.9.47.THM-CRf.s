%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 10.81s
% Output     : CNFRefutation 11.01s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 153 expanded)
%              Number of leaves         :   37 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 355 expanded)
%              Number of equality atoms :   53 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_64,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_105,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    ! [C_39,A_27,D_41,B_35] :
      ( v3_pre_topc(C_39,A_27)
      | k1_tops_1(A_27,C_39) != C_39
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6342,plain,(
    ! [D_408,B_409] :
      ( ~ m1_subset_1(D_408,k1_zfmisc_1(u1_struct_0(B_409)))
      | ~ l1_pre_topc(B_409) ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_6345,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_6342])).

tff(c_6349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6345])).

tff(c_6714,plain,(
    ! [C_429,A_430] :
      ( v3_pre_topc(C_429,A_430)
      | k1_tops_1(A_430,C_429) != C_429
      | ~ m1_subset_1(C_429,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430) ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6720,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_6714])).

tff(c_6724,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_6720])).

tff(c_6725,plain,(
    k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_6724])).

tff(c_42,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_115])).

tff(c_127,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_161,plain,(
    ! [A_75,B_76,C_77] :
      ( k7_subset_1(A_75,B_76,C_77) = k4_xboole_0(B_76,C_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_164,plain,(
    ! [C_77] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_77) = k4_xboole_0('#skF_6',C_77) ),
    inference(resolution,[status(thm)],[c_58,c_161])).

tff(c_663,plain,(
    ! [A_114,B_115] :
      ( k7_subset_1(u1_struct_0(A_114),B_115,k2_tops_1(A_114,B_115)) = k1_tops_1(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_667,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_663])).

tff(c_671,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_164,c_667])).

tff(c_179,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k2_pre_topc(A_79,B_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6984,plain,(
    ! [A_443,B_444,C_445] :
      ( k7_subset_1(u1_struct_0(A_443),k2_pre_topc(A_443,B_444),C_445) = k4_xboole_0(k2_pre_topc(A_443,B_444),C_445)
      | ~ m1_subset_1(B_444,k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ l1_pre_topc(A_443) ) ),
    inference(resolution,[status(thm)],[c_179,c_44])).

tff(c_6988,plain,(
    ! [C_445] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_445) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_445)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_6984])).

tff(c_6993,plain,(
    ! [C_446] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_446) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6988])).

tff(c_70,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_165,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_70])).

tff(c_7003,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6993,c_165])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_390,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden('#skF_1'(A_99,B_100,C_101),B_100)
      | r2_hidden('#skF_2'(A_99,B_100,C_101),C_101)
      | k3_xboole_0(A_99,B_100) = C_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13616,plain,(
    ! [A_619,A_620,B_621,C_622] :
      ( ~ r2_hidden('#skF_1'(A_619,k4_xboole_0(A_620,B_621),C_622),B_621)
      | r2_hidden('#skF_2'(A_619,k4_xboole_0(A_620,B_621),C_622),C_622)
      | k3_xboole_0(A_619,k4_xboole_0(A_620,B_621)) = C_622 ) ),
    inference(resolution,[status(thm)],[c_390,c_22])).

tff(c_13694,plain,(
    ! [A_1,A_620,C_3] :
      ( r2_hidden('#skF_2'(A_1,k4_xboole_0(A_620,A_1),C_3),C_3)
      | k3_xboole_0(A_1,k4_xboole_0(A_620,A_1)) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_13616])).

tff(c_15012,plain,(
    ! [A_662,A_663,C_664] :
      ( r2_hidden('#skF_2'(A_662,k4_xboole_0(A_663,A_662),C_664),C_664)
      | k3_xboole_0(A_662,k4_xboole_0(A_663,A_662)) = C_664 ) ),
    inference(resolution,[status(thm)],[c_18,c_13616])).

tff(c_106,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k4_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [D_58,A_16] :
      ( ~ r2_hidden(D_58,k1_xboole_0)
      | ~ r2_hidden(D_58,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_106])).

tff(c_15332,plain,(
    ! [A_671,A_672,A_673] :
      ( ~ r2_hidden('#skF_2'(A_671,k4_xboole_0(A_672,A_671),k1_xboole_0),A_673)
      | k3_xboole_0(A_671,k4_xboole_0(A_672,A_671)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15012,c_109])).

tff(c_15461,plain,(
    ! [A_674,A_675] : k3_xboole_0(A_674,k4_xboole_0(A_675,A_674)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13694,c_15332])).

tff(c_15626,plain,(
    k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7003,c_15461])).

tff(c_38,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16100,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15626,c_38])).

tff(c_16144,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_671,c_16100])).

tff(c_16146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6725,c_16144])).

tff(c_16147,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_16148,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_54,plain,(
    ! [B_35,D_41,C_39,A_27] :
      ( k1_tops_1(B_35,D_41) = D_41
      | ~ v3_pre_topc(D_41,B_35)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_21533,plain,(
    ! [C_993,A_994] :
      ( ~ m1_subset_1(C_993,k1_zfmisc_1(u1_struct_0(A_994)))
      | ~ l1_pre_topc(A_994)
      | ~ v2_pre_topc(A_994) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_21539,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_21533])).

tff(c_21544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_21539])).

tff(c_21546,plain,(
    ! [B_995,D_996] :
      ( k1_tops_1(B_995,D_996) = D_996
      | ~ v3_pre_topc(D_996,B_995)
      | ~ m1_subset_1(D_996,k1_zfmisc_1(u1_struct_0(B_995)))
      | ~ l1_pre_topc(B_995) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_21552,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_21546])).

tff(c_21556,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_16148,c_21552])).

tff(c_50,plain,(
    ! [A_24,B_26] :
      ( k7_subset_1(u1_struct_0(A_24),k2_pre_topc(A_24,B_26),k1_tops_1(A_24,B_26)) = k2_tops_1(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_21584,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21556,c_50])).

tff(c_21588,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_21584])).

tff(c_21590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16147,c_21588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:57:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.81/3.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.81/3.90  
% 10.81/3.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.81/3.90  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 10.81/3.90  
% 10.81/3.90  %Foreground sorts:
% 10.81/3.90  
% 10.81/3.90  
% 10.81/3.90  %Background operators:
% 10.81/3.90  
% 10.81/3.90  
% 10.81/3.90  %Foreground operators:
% 10.81/3.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.81/3.90  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.81/3.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.81/3.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.81/3.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.81/3.90  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.81/3.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.81/3.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.81/3.90  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.81/3.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.81/3.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.81/3.90  tff('#skF_5', type, '#skF_5': $i).
% 10.81/3.90  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.81/3.90  tff('#skF_6', type, '#skF_6': $i).
% 10.81/3.90  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.81/3.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.81/3.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.81/3.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.81/3.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.81/3.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.81/3.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.81/3.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.81/3.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.81/3.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.81/3.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.81/3.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.81/3.90  
% 11.01/3.92  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 11.01/3.92  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 11.01/3.92  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.01/3.92  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 11.01/3.92  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.01/3.92  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.01/3.92  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 11.01/3.92  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.01/3.92  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.01/3.92  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.01/3.92  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.01/3.92  tff(c_64, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/3.92  tff(c_105, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 11.01/3.92  tff(c_62, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/3.92  tff(c_60, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/3.92  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/3.92  tff(c_52, plain, (![C_39, A_27, D_41, B_35]: (v3_pre_topc(C_39, A_27) | k1_tops_1(A_27, C_39)!=C_39 | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0(B_35))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.01/3.92  tff(c_6342, plain, (![D_408, B_409]: (~m1_subset_1(D_408, k1_zfmisc_1(u1_struct_0(B_409))) | ~l1_pre_topc(B_409))), inference(splitLeft, [status(thm)], [c_52])).
% 11.01/3.92  tff(c_6345, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_6342])).
% 11.01/3.92  tff(c_6349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_6345])).
% 11.01/3.92  tff(c_6714, plain, (![C_429, A_430]: (v3_pre_topc(C_429, A_430) | k1_tops_1(A_430, C_429)!=C_429 | ~m1_subset_1(C_429, k1_zfmisc_1(u1_struct_0(A_430))) | ~l1_pre_topc(A_430) | ~v2_pre_topc(A_430))), inference(splitRight, [status(thm)], [c_52])).
% 11.01/3.92  tff(c_6720, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_6714])).
% 11.01/3.92  tff(c_6724, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_6720])).
% 11.01/3.92  tff(c_6725, plain, (k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_105, c_6724])).
% 11.01/3.92  tff(c_42, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.01/3.92  tff(c_40, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.01/3.92  tff(c_115, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.01/3.92  tff(c_124, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_115])).
% 11.01/3.92  tff(c_127, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_124])).
% 11.01/3.92  tff(c_161, plain, (![A_75, B_76, C_77]: (k7_subset_1(A_75, B_76, C_77)=k4_xboole_0(B_76, C_77) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.01/3.92  tff(c_164, plain, (![C_77]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_77)=k4_xboole_0('#skF_6', C_77))), inference(resolution, [status(thm)], [c_58, c_161])).
% 11.01/3.92  tff(c_663, plain, (![A_114, B_115]: (k7_subset_1(u1_struct_0(A_114), B_115, k2_tops_1(A_114, B_115))=k1_tops_1(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.01/3.92  tff(c_667, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_663])).
% 11.01/3.92  tff(c_671, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_164, c_667])).
% 11.01/3.92  tff(c_179, plain, (![A_79, B_80]: (m1_subset_1(k2_pre_topc(A_79, B_80), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.01/3.92  tff(c_44, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.01/3.92  tff(c_6984, plain, (![A_443, B_444, C_445]: (k7_subset_1(u1_struct_0(A_443), k2_pre_topc(A_443, B_444), C_445)=k4_xboole_0(k2_pre_topc(A_443, B_444), C_445) | ~m1_subset_1(B_444, k1_zfmisc_1(u1_struct_0(A_443))) | ~l1_pre_topc(A_443))), inference(resolution, [status(thm)], [c_179, c_44])).
% 11.01/3.92  tff(c_6988, plain, (![C_445]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_445)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_445) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_6984])).
% 11.01/3.92  tff(c_6993, plain, (![C_446]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_446)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_446))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6988])).
% 11.01/3.92  tff(c_70, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/3.92  tff(c_165, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_105, c_70])).
% 11.01/3.92  tff(c_7003, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6993, c_165])).
% 11.01/3.92  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.01/3.92  tff(c_390, plain, (![A_99, B_100, C_101]: (r2_hidden('#skF_1'(A_99, B_100, C_101), B_100) | r2_hidden('#skF_2'(A_99, B_100, C_101), C_101) | k3_xboole_0(A_99, B_100)=C_101)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.01/3.92  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.01/3.92  tff(c_13616, plain, (![A_619, A_620, B_621, C_622]: (~r2_hidden('#skF_1'(A_619, k4_xboole_0(A_620, B_621), C_622), B_621) | r2_hidden('#skF_2'(A_619, k4_xboole_0(A_620, B_621), C_622), C_622) | k3_xboole_0(A_619, k4_xboole_0(A_620, B_621))=C_622)), inference(resolution, [status(thm)], [c_390, c_22])).
% 11.01/3.92  tff(c_13694, plain, (![A_1, A_620, C_3]: (r2_hidden('#skF_2'(A_1, k4_xboole_0(A_620, A_1), C_3), C_3) | k3_xboole_0(A_1, k4_xboole_0(A_620, A_1))=C_3)), inference(resolution, [status(thm)], [c_18, c_13616])).
% 11.01/3.92  tff(c_15012, plain, (![A_662, A_663, C_664]: (r2_hidden('#skF_2'(A_662, k4_xboole_0(A_663, A_662), C_664), C_664) | k3_xboole_0(A_662, k4_xboole_0(A_663, A_662))=C_664)), inference(resolution, [status(thm)], [c_18, c_13616])).
% 11.01/3.92  tff(c_106, plain, (![D_58, B_59, A_60]: (~r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k4_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.01/3.92  tff(c_109, plain, (![D_58, A_16]: (~r2_hidden(D_58, k1_xboole_0) | ~r2_hidden(D_58, A_16))), inference(superposition, [status(thm), theory('equality')], [c_42, c_106])).
% 11.01/3.92  tff(c_15332, plain, (![A_671, A_672, A_673]: (~r2_hidden('#skF_2'(A_671, k4_xboole_0(A_672, A_671), k1_xboole_0), A_673) | k3_xboole_0(A_671, k4_xboole_0(A_672, A_671))=k1_xboole_0)), inference(resolution, [status(thm)], [c_15012, c_109])).
% 11.01/3.92  tff(c_15461, plain, (![A_674, A_675]: (k3_xboole_0(A_674, k4_xboole_0(A_675, A_674))=k1_xboole_0)), inference(resolution, [status(thm)], [c_13694, c_15332])).
% 11.01/3.92  tff(c_15626, plain, (k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7003, c_15461])).
% 11.01/3.92  tff(c_38, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.01/3.92  tff(c_16100, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15626, c_38])).
% 11.01/3.92  tff(c_16144, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_671, c_16100])).
% 11.01/3.92  tff(c_16146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6725, c_16144])).
% 11.01/3.92  tff(c_16147, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_64])).
% 11.01/3.92  tff(c_16148, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 11.01/3.92  tff(c_54, plain, (![B_35, D_41, C_39, A_27]: (k1_tops_1(B_35, D_41)=D_41 | ~v3_pre_topc(D_41, B_35) | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0(B_35))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.01/3.92  tff(c_21533, plain, (![C_993, A_994]: (~m1_subset_1(C_993, k1_zfmisc_1(u1_struct_0(A_994))) | ~l1_pre_topc(A_994) | ~v2_pre_topc(A_994))), inference(splitLeft, [status(thm)], [c_54])).
% 11.01/3.92  tff(c_21539, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_21533])).
% 11.01/3.92  tff(c_21544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_21539])).
% 11.01/3.92  tff(c_21546, plain, (![B_995, D_996]: (k1_tops_1(B_995, D_996)=D_996 | ~v3_pre_topc(D_996, B_995) | ~m1_subset_1(D_996, k1_zfmisc_1(u1_struct_0(B_995))) | ~l1_pre_topc(B_995))), inference(splitRight, [status(thm)], [c_54])).
% 11.01/3.92  tff(c_21552, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_21546])).
% 11.01/3.92  tff(c_21556, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_16148, c_21552])).
% 11.01/3.92  tff(c_50, plain, (![A_24, B_26]: (k7_subset_1(u1_struct_0(A_24), k2_pre_topc(A_24, B_26), k1_tops_1(A_24, B_26))=k2_tops_1(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.01/3.92  tff(c_21584, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21556, c_50])).
% 11.01/3.92  tff(c_21588, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_21584])).
% 11.01/3.92  tff(c_21590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16147, c_21588])).
% 11.01/3.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.01/3.92  
% 11.01/3.92  Inference rules
% 11.01/3.92  ----------------------
% 11.01/3.92  #Ref     : 0
% 11.01/3.92  #Sup     : 4558
% 11.01/3.92  #Fact    : 0
% 11.01/3.92  #Define  : 0
% 11.01/3.92  #Split   : 20
% 11.01/3.92  #Chain   : 0
% 11.01/3.92  #Close   : 0
% 11.01/3.92  
% 11.01/3.92  Ordering : KBO
% 11.01/3.92  
% 11.01/3.92  Simplification rules
% 11.01/3.92  ----------------------
% 11.01/3.92  #Subsume      : 1259
% 11.01/3.92  #Demod        : 3625
% 11.01/3.92  #Tautology    : 1581
% 11.01/3.92  #SimpNegUnit  : 192
% 11.01/3.92  #BackRed      : 97
% 11.01/3.92  
% 11.01/3.92  #Partial instantiations: 0
% 11.01/3.92  #Strategies tried      : 1
% 11.01/3.92  
% 11.01/3.92  Timing (in seconds)
% 11.01/3.92  ----------------------
% 11.01/3.92  Preprocessing        : 0.34
% 11.01/3.92  Parsing              : 0.17
% 11.01/3.92  CNF conversion       : 0.03
% 11.01/3.92  Main loop            : 2.80
% 11.01/3.92  Inferencing          : 0.85
% 11.01/3.92  Reduction            : 1.01
% 11.01/3.92  Demodulation         : 0.74
% 11.01/3.92  BG Simplification    : 0.09
% 11.01/3.92  Subsumption          : 0.66
% 11.01/3.93  Abstraction          : 0.12
% 11.01/3.93  MUC search           : 0.00
% 11.01/3.93  Cooper               : 0.00
% 11.01/3.93  Total                : 3.18
% 11.01/3.93  Index Insertion      : 0.00
% 11.01/3.93  Index Deletion       : 0.00
% 11.01/3.93  Index Matching       : 0.00
% 11.01/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
