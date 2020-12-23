%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:32 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 145 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 266 expanded)
%              Number of equality atoms :   61 (  94 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6758,plain,(
    ! [A_221,B_222,C_223] :
      ( k7_subset_1(A_221,B_222,C_223) = k4_xboole_0(B_222,C_223)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(A_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6761,plain,(
    ! [C_223] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_223) = k4_xboole_0('#skF_2',C_223) ),
    inference(resolution,[status(thm)],[c_40,c_6758])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_102,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2115,plain,(
    ! [B_124,A_125] :
      ( v4_pre_topc(B_124,A_125)
      | k2_pre_topc(A_125,B_124) != B_124
      | ~ v2_pre_topc(A_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2121,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2115])).

tff(c_2125,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_2121])).

tff(c_2126,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2125])).

tff(c_2338,plain,(
    ! [A_128,B_129] :
      ( k4_subset_1(u1_struct_0(A_128),B_129,k2_tops_1(A_128,B_129)) = k2_pre_topc(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2342,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2338])).

tff(c_2346,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2342])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_311,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_52])).

tff(c_585,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,B_77,C_78) = k4_xboole_0(B_77,C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_702,plain,(
    ! [C_83] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_83) = k4_xboole_0('#skF_2',C_83) ),
    inference(resolution,[status(thm)],[c_40,c_585])).

tff(c_714,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_702])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_211,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_228,plain,(
    ! [A_58] : k3_xboole_0(k1_xboole_0,A_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_211])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [A_58] : k3_xboole_0(A_58,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2])).

tff(c_319,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_328,plain,(
    ! [A_58] : k5_xboole_0(A_58,k1_xboole_0) = k4_xboole_0(A_58,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_319])).

tff(c_343,plain,(
    ! [A_58] : k5_xboole_0(A_58,k1_xboole_0) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_328])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_103])).

tff(c_451,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_463,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_451])).

tff(c_475,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_463])).

tff(c_866,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_475])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_tops_1(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2084,plain,(
    ! [A_120,B_121,C_122] :
      ( k4_subset_1(A_120,B_121,C_122) = k2_xboole_0(B_121,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(A_120))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6138,plain,(
    ! [A_187,B_188,B_189] :
      ( k4_subset_1(u1_struct_0(A_187),B_188,k2_tops_1(A_187,B_189)) = k2_xboole_0(B_188,k2_tops_1(A_187,B_189))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(resolution,[status(thm)],[c_30,c_2084])).

tff(c_6142,plain,(
    ! [B_189] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_189)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_6138])).

tff(c_6150,plain,(
    ! [B_190] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_190)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6142])).

tff(c_6157,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_6150])).

tff(c_6162,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_866,c_6157])).

tff(c_6164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2126,c_6162])).

tff(c_6165,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6908,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6761,c_6165])).

tff(c_6166,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_8074,plain,(
    ! [A_263,B_264] :
      ( r1_tarski(k2_tops_1(A_263,B_264),B_264)
      | ~ v4_pre_topc(B_264,A_263)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8078,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_8074])).

tff(c_8082,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6166,c_8078])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8090,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8082,c_6])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8112,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8090,c_18])).

tff(c_8127,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_8112])).

tff(c_8331,plain,(
    ! [A_270,B_271] :
      ( k7_subset_1(u1_struct_0(A_270),B_271,k2_tops_1(A_270,B_271)) = k1_tops_1(A_270,B_271)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8335,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_8331])).

tff(c_8339,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6761,c_8335])).

tff(c_8361,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8339,c_18])).

tff(c_8375,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8127,c_8361])).

tff(c_8377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6908,c_8375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.23  
% 5.70/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.23  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.70/2.23  
% 5.70/2.23  %Foreground sorts:
% 5.70/2.23  
% 5.70/2.23  
% 5.70/2.23  %Background operators:
% 5.70/2.23  
% 5.70/2.23  
% 5.70/2.23  %Foreground operators:
% 5.70/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.70/2.23  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.70/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.70/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.70/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.70/2.23  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.70/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.23  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.70/2.23  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.70/2.23  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.70/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.70/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.70/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.70/2.23  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.70/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.70/2.23  
% 5.70/2.25  tff(f_120, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.70/2.25  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.70/2.25  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.70/2.25  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.70/2.25  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.70/2.25  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.70/2.25  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.70/2.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.70/2.25  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.70/2.25  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.70/2.25  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.70/2.25  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.70/2.25  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.70/2.25  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.70/2.25  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.70/2.25  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.70/2.25  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.70/2.25  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.70/2.25  tff(c_6758, plain, (![A_221, B_222, C_223]: (k7_subset_1(A_221, B_222, C_223)=k4_xboole_0(B_222, C_223) | ~m1_subset_1(B_222, k1_zfmisc_1(A_221)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.70/2.25  tff(c_6761, plain, (![C_223]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_223)=k4_xboole_0('#skF_2', C_223))), inference(resolution, [status(thm)], [c_40, c_6758])).
% 5.70/2.25  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.70/2.25  tff(c_102, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.70/2.25  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.70/2.25  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.70/2.25  tff(c_2115, plain, (![B_124, A_125]: (v4_pre_topc(B_124, A_125) | k2_pre_topc(A_125, B_124)!=B_124 | ~v2_pre_topc(A_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.70/2.25  tff(c_2121, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2115])).
% 5.70/2.25  tff(c_2125, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_2121])).
% 5.70/2.25  tff(c_2126, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_102, c_2125])).
% 5.70/2.25  tff(c_2338, plain, (![A_128, B_129]: (k4_subset_1(u1_struct_0(A_128), B_129, k2_tops_1(A_128, B_129))=k2_pre_topc(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.70/2.25  tff(c_2342, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2338])).
% 5.70/2.25  tff(c_2346, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2342])).
% 5.70/2.25  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.70/2.25  tff(c_311, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_102, c_52])).
% 5.70/2.25  tff(c_585, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, B_77, C_78)=k4_xboole_0(B_77, C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.70/2.25  tff(c_702, plain, (![C_83]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_83)=k4_xboole_0('#skF_2', C_83))), inference(resolution, [status(thm)], [c_40, c_585])).
% 5.70/2.25  tff(c_714, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_311, c_702])).
% 5.70/2.25  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.70/2.25  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.25  tff(c_211, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.70/2.25  tff(c_228, plain, (![A_58]: (k3_xboole_0(k1_xboole_0, A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_211])).
% 5.70/2.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.70/2.25  tff(c_233, plain, (![A_58]: (k3_xboole_0(A_58, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_228, c_2])).
% 5.70/2.25  tff(c_319, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.70/2.25  tff(c_328, plain, (![A_58]: (k5_xboole_0(A_58, k1_xboole_0)=k4_xboole_0(A_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_233, c_319])).
% 5.70/2.25  tff(c_343, plain, (![A_58]: (k5_xboole_0(A_58, k1_xboole_0)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_328])).
% 5.70/2.25  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.70/2.25  tff(c_103, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.70/2.25  tff(c_118, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_103])).
% 5.70/2.25  tff(c_451, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.70/2.25  tff(c_463, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k5_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_118, c_451])).
% 5.70/2.25  tff(c_475, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(A_10, B_11))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_463])).
% 5.70/2.25  tff(c_866, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_714, c_475])).
% 5.70/2.25  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(k2_tops_1(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.70/2.25  tff(c_2084, plain, (![A_120, B_121, C_122]: (k4_subset_1(A_120, B_121, C_122)=k2_xboole_0(B_121, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(A_120)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.70/2.25  tff(c_6138, plain, (![A_187, B_188, B_189]: (k4_subset_1(u1_struct_0(A_187), B_188, k2_tops_1(A_187, B_189))=k2_xboole_0(B_188, k2_tops_1(A_187, B_189)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(resolution, [status(thm)], [c_30, c_2084])).
% 5.70/2.25  tff(c_6142, plain, (![B_189]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_189))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_6138])).
% 5.70/2.25  tff(c_6150, plain, (![B_190]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_190))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6142])).
% 5.70/2.25  tff(c_6157, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_6150])).
% 5.70/2.25  tff(c_6162, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_866, c_6157])).
% 5.70/2.25  tff(c_6164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2126, c_6162])).
% 5.70/2.25  tff(c_6165, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.70/2.25  tff(c_6908, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6761, c_6165])).
% 5.70/2.25  tff(c_6166, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 5.70/2.25  tff(c_8074, plain, (![A_263, B_264]: (r1_tarski(k2_tops_1(A_263, B_264), B_264) | ~v4_pre_topc(B_264, A_263) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.70/2.25  tff(c_8078, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_8074])).
% 5.70/2.25  tff(c_8082, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6166, c_8078])).
% 5.70/2.25  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.70/2.25  tff(c_8090, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_8082, c_6])).
% 5.70/2.25  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.70/2.25  tff(c_8112, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8090, c_18])).
% 5.70/2.25  tff(c_8127, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_8112])).
% 5.70/2.25  tff(c_8331, plain, (![A_270, B_271]: (k7_subset_1(u1_struct_0(A_270), B_271, k2_tops_1(A_270, B_271))=k1_tops_1(A_270, B_271) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.70/2.25  tff(c_8335, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_8331])).
% 5.70/2.25  tff(c_8339, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6761, c_8335])).
% 5.70/2.25  tff(c_8361, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8339, c_18])).
% 5.70/2.25  tff(c_8375, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8127, c_8361])).
% 5.70/2.25  tff(c_8377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6908, c_8375])).
% 5.70/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.25  
% 5.70/2.25  Inference rules
% 5.70/2.25  ----------------------
% 5.70/2.25  #Ref     : 0
% 5.70/2.25  #Sup     : 2044
% 5.70/2.25  #Fact    : 0
% 5.70/2.25  #Define  : 0
% 5.70/2.25  #Split   : 4
% 5.70/2.25  #Chain   : 0
% 5.70/2.25  #Close   : 0
% 5.70/2.25  
% 5.70/2.25  Ordering : KBO
% 5.70/2.25  
% 5.70/2.25  Simplification rules
% 5.70/2.25  ----------------------
% 5.70/2.25  #Subsume      : 145
% 5.70/2.25  #Demod        : 2908
% 5.70/2.25  #Tautology    : 1649
% 5.70/2.25  #SimpNegUnit  : 12
% 5.70/2.25  #BackRed      : 1
% 5.70/2.25  
% 5.70/2.25  #Partial instantiations: 0
% 5.70/2.25  #Strategies tried      : 1
% 5.70/2.25  
% 5.70/2.25  Timing (in seconds)
% 5.70/2.25  ----------------------
% 5.70/2.25  Preprocessing        : 0.33
% 5.70/2.25  Parsing              : 0.17
% 5.70/2.25  CNF conversion       : 0.02
% 5.70/2.25  Main loop            : 1.12
% 5.70/2.25  Inferencing          : 0.31
% 5.70/2.25  Reduction            : 0.57
% 5.70/2.25  Demodulation         : 0.48
% 5.70/2.25  BG Simplification    : 0.03
% 5.70/2.25  Subsumption          : 0.15
% 5.70/2.25  Abstraction          : 0.06
% 5.70/2.25  MUC search           : 0.00
% 5.70/2.25  Cooper               : 0.00
% 5.70/2.25  Total                : 1.48
% 5.70/2.25  Index Insertion      : 0.00
% 5.70/2.25  Index Deletion       : 0.00
% 5.70/2.25  Index Matching       : 0.00
% 5.70/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
