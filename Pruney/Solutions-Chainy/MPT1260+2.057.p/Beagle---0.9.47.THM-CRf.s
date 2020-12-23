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
% DateTime   : Thu Dec  3 10:21:07 EST 2020

% Result     : Theorem 11.03s
% Output     : CNFRefutation 11.27s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 522 expanded)
%              Number of leaves         :   41 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  227 (1072 expanded)
%              Number of equality atoms :   92 ( 341 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_108,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_58,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_118,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_327,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_658,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_subset_1(A_98,B_99,C_100) = k4_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_664,plain,(
    ! [C_100] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_100) = k4_xboole_0('#skF_2',C_100) ),
    inference(resolution,[status(thm)],[c_46,c_658])).

tff(c_2082,plain,(
    ! [A_156,B_157] :
      ( k7_subset_1(u1_struct_0(A_156),B_157,k2_tops_1(A_156,B_157)) = k1_tops_1(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2104,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2082])).

tff(c_2128,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_664,c_2104])).

tff(c_830,plain,(
    ! [C_110] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_110) = k4_xboole_0('#skF_2',C_110) ),
    inference(resolution,[status(thm)],[c_46,c_658])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k7_subset_1(A_18,B_19,C_20),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_836,plain,(
    ! [C_110] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_110),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_26])).

tff(c_842,plain,(
    ! [C_110] : m1_subset_1(k4_xboole_0('#skF_2',C_110),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_836])).

tff(c_2141,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_842])).

tff(c_40,plain,(
    ! [C_50,A_38,D_52,B_46] :
      ( v3_pre_topc(C_50,A_38)
      | k1_tops_1(A_38,C_50) != C_50
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(B_46)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3257,plain,(
    ! [D_174,B_175] :
      ( ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0(B_175)))
      | ~ l1_pre_topc(B_175) ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_3260,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2141,c_3257])).

tff(c_3293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3260])).

tff(c_3444,plain,(
    ! [C_178,A_179] :
      ( v3_pre_topc(C_178,A_179)
      | k1_tops_1(A_179,C_178) != C_178
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179) ) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_3479,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_3444])).

tff(c_3506,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3479])).

tff(c_3507,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_3506])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_227,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_242,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_18,c_227])).

tff(c_2147,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_242])).

tff(c_2160,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2,c_2147])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2150,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_22])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_241,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_227])).

tff(c_3520,plain,
    ( k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2150,c_241])).

tff(c_3538,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_3520])).

tff(c_3539,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3507,c_3538])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_243,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_347,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_362,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_347])).

tff(c_373,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_362])).

tff(c_1106,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1(k2_pre_topc(A_126,B_127),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_792,plain,(
    ! [A_105,B_106,C_107] :
      ( m1_subset_1(k7_subset_1(A_105,B_106,C_107),k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_797,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_792])).

tff(c_860,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_1111,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1106,c_860])).

tff(c_1118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1111])).

tff(c_1120,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_28,plain,(
    ! [A_21,B_22,C_23] :
      ( k7_subset_1(A_21,B_22,C_23) = k4_xboole_0(B_22,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1906,plain,(
    ! [C_153] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_153) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_153) ),
    inference(resolution,[status(thm)],[c_1120,c_28])).

tff(c_1921,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_1906])).

tff(c_1139,plain,(
    ! [C_23] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_23) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_23) ),
    inference(resolution,[status(thm)],[c_1120,c_28])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1270,plain,(
    ! [A_133,B_134,C_135] :
      ( k9_subset_1(A_133,B_134,C_135) = k3_xboole_0(B_134,C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5348,plain,(
    ! [A_215,B_216,B_217] :
      ( k9_subset_1(A_215,B_216,k3_subset_1(A_215,B_217)) = k3_xboole_0(B_216,k3_subset_1(A_215,B_217))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_215)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1270])).

tff(c_5390,plain,(
    ! [B_216] : k9_subset_1(u1_struct_0('#skF_1'),B_216,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_216,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_5348])).

tff(c_2316,plain,(
    ! [A_158,B_159,C_160] :
      ( k9_subset_1(A_158,B_159,k3_subset_1(A_158,C_160)) = k7_subset_1(A_158,B_159,C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(A_158))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2349,plain,(
    ! [B_159] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_159,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),B_159,'#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2316])).

tff(c_7630,plain,(
    ! [B_260] :
      ( k3_xboole_0(B_260,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),B_260,'#skF_2')
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5390,c_2349])).

tff(c_7679,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1120,c_7630])).

tff(c_7715,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1921,c_1139,c_7679])).

tff(c_430,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_477,plain,(
    ! [A_88,B_89] : r1_tarski(k3_xboole_0(A_88,B_89),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_18])).

tff(c_513,plain,(
    ! [B_90,A_91] : r1_tarski(k3_xboole_0(B_90,A_91),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_477])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_544,plain,(
    ! [B_90,A_91] : k3_xboole_0(k3_xboole_0(B_90,A_91),A_91) = k3_xboole_0(B_90,A_91) ),
    inference(resolution,[status(thm)],[c_513,c_16])).

tff(c_18510,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7715,c_544])).

tff(c_18575,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7715,c_18510])).

tff(c_1119,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_1142,plain,(
    ! [C_23] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_23) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_23) ),
    inference(resolution,[status(thm)],[c_1119,c_28])).

tff(c_12685,plain,(
    ! [C_322] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_322) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_322) ),
    inference(resolution,[status(thm)],[c_1119,c_28])).

tff(c_12706,plain,(
    ! [C_322] :
      ( m1_subset_1(k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_322),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12685,c_26])).

tff(c_12724,plain,(
    ! [C_323] : m1_subset_1(k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_323),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_12706])).

tff(c_12818,plain,(
    ! [B_324] : m1_subset_1(k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_324),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_12724])).

tff(c_5469,plain,(
    ! [B_159] :
      ( k3_xboole_0(B_159,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),B_159,'#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5390,c_2349])).

tff(c_20012,plain,(
    ! [B_387] : k3_xboole_0(k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_387),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_387),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12818,c_5469])).

tff(c_20101,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20012,c_544])).

tff(c_20224,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18575,c_1142,c_18575,c_20101])).

tff(c_706,plain,(
    ! [A_103,B_104] : k3_xboole_0(k4_xboole_0(A_103,B_104),A_103) = k4_xboole_0(A_103,B_104) ),
    inference(resolution,[status(thm)],[c_18,c_227])).

tff(c_365,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_347])).

tff(c_712,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_365])).

tff(c_775,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_712])).

tff(c_20266,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20224,c_775])).

tff(c_20300,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_373,c_20266])).

tff(c_20302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3539,c_20300])).

tff(c_20303,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_20635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_20303])).

tff(c_20636,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_20806,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20636,c_52])).

tff(c_21308,plain,(
    ! [A_443,B_444,C_445] :
      ( k7_subset_1(A_443,B_444,C_445) = k4_xboole_0(B_444,C_445)
      | ~ m1_subset_1(B_444,k1_zfmisc_1(A_443)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_21314,plain,(
    ! [C_445] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_445) = k4_xboole_0('#skF_2',C_445) ),
    inference(resolution,[status(thm)],[c_46,c_21308])).

tff(c_21819,plain,(
    ! [A_470,B_471] :
      ( k7_subset_1(u1_struct_0(A_470),B_471,k2_tops_1(A_470,B_471)) = k1_tops_1(A_470,B_471)
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_pre_topc(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21837,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_21819])).

tff(c_21855,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_21314,c_21837])).

tff(c_21364,plain,(
    ! [A_450,B_451,C_452] :
      ( m1_subset_1(k7_subset_1(A_450,B_451,C_452),k1_zfmisc_1(A_450))
      | ~ m1_subset_1(B_451,k1_zfmisc_1(A_450)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21371,plain,(
    ! [C_445] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_445),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21314,c_21364])).

tff(c_21375,plain,(
    ! [C_445] : m1_subset_1(k4_xboole_0('#skF_2',C_445),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_21371])).

tff(c_21871,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_21855,c_21375])).

tff(c_42,plain,(
    ! [B_46,D_52,C_50,A_38] :
      ( k1_tops_1(B_46,D_52) = D_52
      | ~ v3_pre_topc(D_52,B_46)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(B_46)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_23381,plain,(
    ! [C_496,A_497] :
      ( ~ m1_subset_1(C_496,k1_zfmisc_1(u1_struct_0(A_497)))
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497) ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_23384,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_21871,c_23381])).

tff(c_23414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_23384])).

tff(c_24003,plain,(
    ! [B_506,D_507] :
      ( k1_tops_1(B_506,D_507) = D_507
      | ~ v3_pre_topc(D_507,B_506)
      | ~ m1_subset_1(D_507,k1_zfmisc_1(u1_struct_0(B_506)))
      | ~ l1_pre_topc(B_506) ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_24032,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_24003])).

tff(c_24053,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20636,c_24032])).

tff(c_38,plain,(
    ! [A_35,B_37] :
      ( k7_subset_1(u1_struct_0(A_35),k2_pre_topc(A_35,B_37),k1_tops_1(A_35,B_37)) = k2_tops_1(A_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24071,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24053,c_38])).

tff(c_24075,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_24071])).

tff(c_24077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20806,c_24075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.03/4.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.56  
% 11.03/4.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.56  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.27/4.56  
% 11.27/4.56  %Foreground sorts:
% 11.27/4.56  
% 11.27/4.56  
% 11.27/4.56  %Background operators:
% 11.27/4.56  
% 11.27/4.56  
% 11.27/4.56  %Foreground operators:
% 11.27/4.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.27/4.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.27/4.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.27/4.56  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.27/4.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.27/4.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.27/4.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.27/4.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.27/4.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.27/4.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.27/4.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.27/4.56  tff('#skF_2', type, '#skF_2': $i).
% 11.27/4.56  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.27/4.56  tff('#skF_1', type, '#skF_1': $i).
% 11.27/4.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.27/4.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.27/4.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.27/4.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.27/4.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.27/4.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.27/4.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.27/4.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.27/4.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.27/4.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.27/4.56  
% 11.27/4.59  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 11.27/4.59  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.27/4.59  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 11.27/4.59  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 11.27/4.59  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 11.27/4.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.27/4.59  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.27/4.59  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.27/4.59  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.27/4.59  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.27/4.59  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.27/4.59  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.27/4.59  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.27/4.59  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.27/4.59  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.27/4.59  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 11.27/4.59  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.27/4.59  tff(c_58, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.27/4.59  tff(c_118, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 11.27/4.59  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.27/4.59  tff(c_327, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 11.27/4.59  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.27/4.59  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.27/4.59  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.27/4.59  tff(c_658, plain, (![A_98, B_99, C_100]: (k7_subset_1(A_98, B_99, C_100)=k4_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.27/4.59  tff(c_664, plain, (![C_100]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_100)=k4_xboole_0('#skF_2', C_100))), inference(resolution, [status(thm)], [c_46, c_658])).
% 11.27/4.59  tff(c_2082, plain, (![A_156, B_157]: (k7_subset_1(u1_struct_0(A_156), B_157, k2_tops_1(A_156, B_157))=k1_tops_1(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.27/4.59  tff(c_2104, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2082])).
% 11.27/4.59  tff(c_2128, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_664, c_2104])).
% 11.27/4.59  tff(c_830, plain, (![C_110]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_110)=k4_xboole_0('#skF_2', C_110))), inference(resolution, [status(thm)], [c_46, c_658])).
% 11.27/4.59  tff(c_26, plain, (![A_18, B_19, C_20]: (m1_subset_1(k7_subset_1(A_18, B_19, C_20), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.27/4.59  tff(c_836, plain, (![C_110]: (m1_subset_1(k4_xboole_0('#skF_2', C_110), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_830, c_26])).
% 11.27/4.59  tff(c_842, plain, (![C_110]: (m1_subset_1(k4_xboole_0('#skF_2', C_110), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_836])).
% 11.27/4.59  tff(c_2141, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2128, c_842])).
% 11.27/4.59  tff(c_40, plain, (![C_50, A_38, D_52, B_46]: (v3_pre_topc(C_50, A_38) | k1_tops_1(A_38, C_50)!=C_50 | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(B_46))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(B_46) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.27/4.59  tff(c_3257, plain, (![D_174, B_175]: (~m1_subset_1(D_174, k1_zfmisc_1(u1_struct_0(B_175))) | ~l1_pre_topc(B_175))), inference(splitLeft, [status(thm)], [c_40])).
% 11.27/4.59  tff(c_3260, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2141, c_3257])).
% 11.27/4.59  tff(c_3293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3260])).
% 11.27/4.59  tff(c_3444, plain, (![C_178, A_179]: (v3_pre_topc(C_178, A_179) | k1_tops_1(A_179, C_178)!=C_178 | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179))), inference(splitRight, [status(thm)], [c_40])).
% 11.27/4.59  tff(c_3479, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_3444])).
% 11.27/4.59  tff(c_3506, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3479])).
% 11.27/4.59  tff(c_3507, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_327, c_3506])).
% 11.27/4.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.27/4.59  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.27/4.59  tff(c_227, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.27/4.59  tff(c_242, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_227])).
% 11.27/4.59  tff(c_2147, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2128, c_242])).
% 11.27/4.59  tff(c_2160, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2, c_2147])).
% 11.27/4.59  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.27/4.59  tff(c_2150, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2128, c_22])).
% 11.27/4.59  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.27/4.59  tff(c_241, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_227])).
% 11.27/4.59  tff(c_3520, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2150, c_241])).
% 11.27/4.59  tff(c_3538, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_3520])).
% 11.27/4.59  tff(c_3539, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3507, c_3538])).
% 11.27/4.59  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.27/4.59  tff(c_119, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.27/4.59  tff(c_131, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_119])).
% 11.27/4.59  tff(c_243, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_227])).
% 11.27/4.59  tff(c_347, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.27/4.59  tff(c_362, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_243, c_347])).
% 11.27/4.59  tff(c_373, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_362])).
% 11.27/4.59  tff(c_1106, plain, (![A_126, B_127]: (m1_subset_1(k2_pre_topc(A_126, B_127), k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.27/4.59  tff(c_792, plain, (![A_105, B_106, C_107]: (m1_subset_1(k7_subset_1(A_105, B_106, C_107), k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.27/4.59  tff(c_797, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_118, c_792])).
% 11.27/4.59  tff(c_860, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_797])).
% 11.27/4.59  tff(c_1111, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1106, c_860])).
% 11.27/4.59  tff(c_1118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1111])).
% 11.27/4.59  tff(c_1120, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_797])).
% 11.27/4.59  tff(c_28, plain, (![A_21, B_22, C_23]: (k7_subset_1(A_21, B_22, C_23)=k4_xboole_0(B_22, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.27/4.59  tff(c_1906, plain, (![C_153]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_153)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_153))), inference(resolution, [status(thm)], [c_1120, c_28])).
% 11.27/4.59  tff(c_1921, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_1906])).
% 11.27/4.59  tff(c_1139, plain, (![C_23]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_23)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_23))), inference(resolution, [status(thm)], [c_1120, c_28])).
% 11.27/4.59  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k3_subset_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.27/4.59  tff(c_1270, plain, (![A_133, B_134, C_135]: (k9_subset_1(A_133, B_134, C_135)=k3_xboole_0(B_134, C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.27/4.59  tff(c_5348, plain, (![A_215, B_216, B_217]: (k9_subset_1(A_215, B_216, k3_subset_1(A_215, B_217))=k3_xboole_0(B_216, k3_subset_1(A_215, B_217)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_215)))), inference(resolution, [status(thm)], [c_24, c_1270])).
% 11.27/4.59  tff(c_5390, plain, (![B_216]: (k9_subset_1(u1_struct_0('#skF_1'), B_216, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_216, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_5348])).
% 11.27/4.59  tff(c_2316, plain, (![A_158, B_159, C_160]: (k9_subset_1(A_158, B_159, k3_subset_1(A_158, C_160))=k7_subset_1(A_158, B_159, C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(A_158)) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.27/4.59  tff(c_2349, plain, (![B_159]: (k9_subset_1(u1_struct_0('#skF_1'), B_159, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), B_159, '#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_46, c_2316])).
% 11.27/4.59  tff(c_7630, plain, (![B_260]: (k3_xboole_0(B_260, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), B_260, '#skF_2') | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_5390, c_2349])).
% 11.27/4.59  tff(c_7679, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1120, c_7630])).
% 11.27/4.59  tff(c_7715, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1921, c_1139, c_7679])).
% 11.27/4.59  tff(c_430, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.27/4.59  tff(c_477, plain, (![A_88, B_89]: (r1_tarski(k3_xboole_0(A_88, B_89), A_88))), inference(superposition, [status(thm), theory('equality')], [c_430, c_18])).
% 11.27/4.59  tff(c_513, plain, (![B_90, A_91]: (r1_tarski(k3_xboole_0(B_90, A_91), A_91))), inference(superposition, [status(thm), theory('equality')], [c_2, c_477])).
% 11.27/4.59  tff(c_16, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.27/4.59  tff(c_544, plain, (![B_90, A_91]: (k3_xboole_0(k3_xboole_0(B_90, A_91), A_91)=k3_xboole_0(B_90, A_91))), inference(resolution, [status(thm)], [c_513, c_16])).
% 11.27/4.59  tff(c_18510, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7715, c_544])).
% 11.27/4.59  tff(c_18575, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7715, c_18510])).
% 11.27/4.59  tff(c_1119, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_797])).
% 11.27/4.59  tff(c_1142, plain, (![C_23]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_23)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_23))), inference(resolution, [status(thm)], [c_1119, c_28])).
% 11.27/4.59  tff(c_12685, plain, (![C_322]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), C_322)=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_322))), inference(resolution, [status(thm)], [c_1119, c_28])).
% 11.27/4.59  tff(c_12706, plain, (![C_322]: (m1_subset_1(k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_322), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_12685, c_26])).
% 11.27/4.59  tff(c_12724, plain, (![C_323]: (m1_subset_1(k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), C_323), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_12706])).
% 11.27/4.59  tff(c_12818, plain, (![B_324]: (m1_subset_1(k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_324), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_12724])).
% 11.27/4.59  tff(c_5469, plain, (![B_159]: (k3_xboole_0(B_159, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), B_159, '#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_5390, c_2349])).
% 11.27/4.59  tff(c_20012, plain, (![B_387]: (k3_xboole_0(k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_387), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_387), '#skF_2'))), inference(resolution, [status(thm)], [c_12818, c_5469])).
% 11.27/4.59  tff(c_20101, plain, (k7_subset_1(u1_struct_0('#skF_1'), k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_20012, c_544])).
% 11.27/4.59  tff(c_20224, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18575, c_1142, c_18575, c_20101])).
% 11.27/4.59  tff(c_706, plain, (![A_103, B_104]: (k3_xboole_0(k4_xboole_0(A_103, B_104), A_103)=k4_xboole_0(A_103, B_104))), inference(resolution, [status(thm)], [c_18, c_227])).
% 11.27/4.59  tff(c_365, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_347])).
% 11.27/4.59  tff(c_712, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k4_xboole_0(A_103, k4_xboole_0(A_103, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_706, c_365])).
% 11.27/4.59  tff(c_775, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_712])).
% 11.27/4.59  tff(c_20266, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20224, c_775])).
% 11.27/4.59  tff(c_20300, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_373, c_20266])).
% 11.27/4.59  tff(c_20302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3539, c_20300])).
% 11.27/4.59  tff(c_20303, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 11.27/4.59  tff(c_20635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_20303])).
% 11.27/4.59  tff(c_20636, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 11.27/4.59  tff(c_20806, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20636, c_52])).
% 11.27/4.59  tff(c_21308, plain, (![A_443, B_444, C_445]: (k7_subset_1(A_443, B_444, C_445)=k4_xboole_0(B_444, C_445) | ~m1_subset_1(B_444, k1_zfmisc_1(A_443)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.27/4.59  tff(c_21314, plain, (![C_445]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_445)=k4_xboole_0('#skF_2', C_445))), inference(resolution, [status(thm)], [c_46, c_21308])).
% 11.27/4.59  tff(c_21819, plain, (![A_470, B_471]: (k7_subset_1(u1_struct_0(A_470), B_471, k2_tops_1(A_470, B_471))=k1_tops_1(A_470, B_471) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_pre_topc(A_470))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.27/4.59  tff(c_21837, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_21819])).
% 11.27/4.59  tff(c_21855, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_21314, c_21837])).
% 11.27/4.59  tff(c_21364, plain, (![A_450, B_451, C_452]: (m1_subset_1(k7_subset_1(A_450, B_451, C_452), k1_zfmisc_1(A_450)) | ~m1_subset_1(B_451, k1_zfmisc_1(A_450)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.27/4.59  tff(c_21371, plain, (![C_445]: (m1_subset_1(k4_xboole_0('#skF_2', C_445), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_21314, c_21364])).
% 11.27/4.59  tff(c_21375, plain, (![C_445]: (m1_subset_1(k4_xboole_0('#skF_2', C_445), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_21371])).
% 11.27/4.59  tff(c_21871, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_21855, c_21375])).
% 11.27/4.59  tff(c_42, plain, (![B_46, D_52, C_50, A_38]: (k1_tops_1(B_46, D_52)=D_52 | ~v3_pre_topc(D_52, B_46) | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(B_46))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(B_46) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.27/4.59  tff(c_23381, plain, (![C_496, A_497]: (~m1_subset_1(C_496, k1_zfmisc_1(u1_struct_0(A_497))) | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497))), inference(splitLeft, [status(thm)], [c_42])).
% 11.27/4.59  tff(c_23384, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_21871, c_23381])).
% 11.27/4.59  tff(c_23414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_23384])).
% 11.27/4.59  tff(c_24003, plain, (![B_506, D_507]: (k1_tops_1(B_506, D_507)=D_507 | ~v3_pre_topc(D_507, B_506) | ~m1_subset_1(D_507, k1_zfmisc_1(u1_struct_0(B_506))) | ~l1_pre_topc(B_506))), inference(splitRight, [status(thm)], [c_42])).
% 11.27/4.59  tff(c_24032, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_24003])).
% 11.27/4.59  tff(c_24053, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20636, c_24032])).
% 11.27/4.59  tff(c_38, plain, (![A_35, B_37]: (k7_subset_1(u1_struct_0(A_35), k2_pre_topc(A_35, B_37), k1_tops_1(A_35, B_37))=k2_tops_1(A_35, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.27/4.59  tff(c_24071, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24053, c_38])).
% 11.27/4.59  tff(c_24075, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_24071])).
% 11.27/4.59  tff(c_24077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20806, c_24075])).
% 11.27/4.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.59  
% 11.27/4.59  Inference rules
% 11.27/4.59  ----------------------
% 11.27/4.59  #Ref     : 0
% 11.27/4.59  #Sup     : 5788
% 11.27/4.59  #Fact    : 0
% 11.27/4.59  #Define  : 0
% 11.27/4.59  #Split   : 16
% 11.27/4.59  #Chain   : 0
% 11.27/4.59  #Close   : 0
% 11.27/4.59  
% 11.27/4.59  Ordering : KBO
% 11.27/4.59  
% 11.27/4.59  Simplification rules
% 11.27/4.59  ----------------------
% 11.27/4.59  #Subsume      : 436
% 11.27/4.59  #Demod        : 6704
% 11.27/4.59  #Tautology    : 3407
% 11.27/4.59  #SimpNegUnit  : 80
% 11.27/4.59  #BackRed      : 12
% 11.27/4.59  
% 11.27/4.59  #Partial instantiations: 0
% 11.27/4.59  #Strategies tried      : 1
% 11.27/4.59  
% 11.27/4.59  Timing (in seconds)
% 11.27/4.59  ----------------------
% 11.27/4.59  Preprocessing        : 0.35
% 11.27/4.59  Parsing              : 0.19
% 11.27/4.59  CNF conversion       : 0.02
% 11.27/4.59  Main loop            : 3.46
% 11.27/4.59  Inferencing          : 0.66
% 11.27/4.59  Reduction            : 1.97
% 11.27/4.59  Demodulation         : 1.70
% 11.27/4.59  BG Simplification    : 0.08
% 11.27/4.59  Subsumption          : 0.55
% 11.27/4.59  Abstraction          : 0.16
% 11.27/4.59  MUC search           : 0.00
% 11.27/4.59  Cooper               : 0.00
% 11.27/4.59  Total                : 3.86
% 11.27/4.59  Index Insertion      : 0.00
% 11.27/4.59  Index Deletion       : 0.00
% 11.27/4.59  Index Matching       : 0.00
% 11.27/4.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
