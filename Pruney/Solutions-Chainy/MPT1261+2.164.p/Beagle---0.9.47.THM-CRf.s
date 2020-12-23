%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:35 EST 2020

% Result     : Theorem 17.07s
% Output     : CNFRefutation 17.07s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 187 expanded)
%              Number of leaves         :   42 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 334 expanded)
%              Number of equality atoms :   71 ( 126 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_82688,plain,(
    ! [A_565,B_566,C_567] :
      ( k7_subset_1(A_565,B_566,C_567) = k4_xboole_0(B_566,C_567)
      | ~ m1_subset_1(B_566,k1_zfmisc_1(A_565)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_82695,plain,(
    ! [C_567] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_567) = k4_xboole_0('#skF_2',C_567) ),
    inference(resolution,[status(thm)],[c_42,c_82688])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_233,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2938,plain,(
    ! [B_147,A_148] :
      ( v4_pre_topc(B_147,A_148)
      | k2_pre_topc(A_148,B_147) != B_147
      | ~ v2_pre_topc(A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2944,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2938])).

tff(c_2956,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_2944])).

tff(c_2957,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_2956])).

tff(c_3216,plain,(
    ! [A_153,B_154] :
      ( k4_subset_1(u1_struct_0(A_153),B_154,k2_tops_1(A_153,B_154)) = k2_pre_topc(A_153,B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3220,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_3216])).

tff(c_3230,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3220])).

tff(c_1233,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(A_102,B_103,C_104) = k4_xboole_0(B_103,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1270,plain,(
    ! [C_109] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_109) = k4_xboole_0('#skF_2',C_109) ),
    inference(resolution,[status(thm)],[c_42,c_1233])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_389,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_54])).

tff(c_1276,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_389])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_4,B_5] : k2_xboole_0(k4_xboole_0(A_4,B_5),A_4) = A_4 ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_1306,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_98])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_125,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_4])).

tff(c_165,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [B_54] : k5_xboole_0(B_54,k1_xboole_0) = k2_xboole_0(B_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_165])).

tff(c_180,plain,(
    ! [B_54] : k5_xboole_0(B_54,k1_xboole_0) = B_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_174])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_219,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_225,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = k3_subset_1(A_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_231,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_225])).

tff(c_316,plain,(
    ! [A_66,B_67] :
      ( k3_subset_1(A_66,k3_subset_1(A_66,B_67)) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_320,plain,(
    ! [A_24] : k3_subset_1(A_24,k3_subset_1(A_24,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_316])).

tff(c_325,plain,(
    ! [A_24] : k3_subset_1(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_320])).

tff(c_14,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k2_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_15] : m1_subset_1(A_15,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_232,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_subset_1(A_15,A_15) ),
    inference(resolution,[status(thm)],[c_55,c_219])).

tff(c_329,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_232])).

tff(c_456,plain,(
    ! [A_73,B_74,C_75] : k4_xboole_0(k4_xboole_0(A_73,B_74),C_75) = k4_xboole_0(A_73,k2_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_488,plain,(
    ! [A_15,C_75] : k4_xboole_0(A_15,k2_xboole_0(A_15,C_75)) = k4_xboole_0(k1_xboole_0,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_456])).

tff(c_512,plain,(
    ! [A_76,C_77] : k4_xboole_0(A_76,k2_xboole_0(A_76,C_77)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_488])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_524,plain,(
    ! [A_76,C_77] : k5_xboole_0(k2_xboole_0(A_76,C_77),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_76,C_77),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_12])).

tff(c_557,plain,(
    ! [A_76,C_77] : k2_xboole_0(k2_xboole_0(A_76,C_77),A_76) = k2_xboole_0(A_76,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_524])).

tff(c_1326,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_557])).

tff(c_1335,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1326])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_tops_1(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2659,plain,(
    ! [A_134,B_135,C_136] :
      ( k4_subset_1(A_134,B_135,C_136) = k2_xboole_0(B_135,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_29605,plain,(
    ! [A_351,B_352,B_353] :
      ( k4_subset_1(u1_struct_0(A_351),B_352,k2_tops_1(A_351,B_353)) = k2_xboole_0(B_352,k2_tops_1(A_351,B_353))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351) ) ),
    inference(resolution,[status(thm)],[c_34,c_2659])).

tff(c_29609,plain,(
    ! [B_353] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_353)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_353))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_29605])).

tff(c_82240,plain,(
    ! [B_539] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_539)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_539))
      | ~ m1_subset_1(B_539,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_29609])).

tff(c_82247,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_82240])).

tff(c_82260,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_1335,c_82247])).

tff(c_82262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2957,c_82260])).

tff(c_82263,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_82708,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82695,c_82263])).

tff(c_82264,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_82974,plain,(
    ! [A_579,B_580] :
      ( k2_pre_topc(A_579,B_580) = B_580
      | ~ v4_pre_topc(B_580,A_579)
      | ~ m1_subset_1(B_580,k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ l1_pre_topc(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82977,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_82974])).

tff(c_82988,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_82264,c_82977])).

tff(c_86835,plain,(
    ! [A_658,B_659] :
      ( k7_subset_1(u1_struct_0(A_658),k2_pre_topc(A_658,B_659),k1_tops_1(A_658,B_659)) = k2_tops_1(A_658,B_659)
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0(A_658)))
      | ~ l1_pre_topc(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_86844,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_82988,c_86835])).

tff(c_86848,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_82695,c_86844])).

tff(c_86850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82708,c_86848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.07/10.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.07/10.19  
% 17.07/10.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.07/10.19  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 17.07/10.19  
% 17.07/10.19  %Foreground sorts:
% 17.07/10.19  
% 17.07/10.19  
% 17.07/10.19  %Background operators:
% 17.07/10.19  
% 17.07/10.19  
% 17.07/10.19  %Foreground operators:
% 17.07/10.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.07/10.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.07/10.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.07/10.19  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 17.07/10.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.07/10.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.07/10.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.07/10.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.07/10.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.07/10.19  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.07/10.19  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 17.07/10.19  tff('#skF_2', type, '#skF_2': $i).
% 17.07/10.19  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 17.07/10.19  tff('#skF_1', type, '#skF_1': $i).
% 17.07/10.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.07/10.19  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 17.07/10.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.07/10.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.07/10.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.07/10.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.07/10.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.07/10.19  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 17.07/10.19  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 17.07/10.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.07/10.19  
% 17.07/10.21  tff(f_124, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 17.07/10.21  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 17.07/10.21  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 17.07/10.21  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 17.07/10.21  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 17.07/10.21  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.07/10.21  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 17.07/10.21  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 17.07/10.21  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 17.07/10.21  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 17.07/10.21  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 17.07/10.21  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 17.07/10.21  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 17.07/10.21  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 17.07/10.21  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 17.07/10.21  tff(f_90, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 17.07/10.21  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.07/10.21  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 17.07/10.21  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 17.07/10.21  tff(c_82688, plain, (![A_565, B_566, C_567]: (k7_subset_1(A_565, B_566, C_567)=k4_xboole_0(B_566, C_567) | ~m1_subset_1(B_566, k1_zfmisc_1(A_565)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.07/10.21  tff(c_82695, plain, (![C_567]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_567)=k4_xboole_0('#skF_2', C_567))), inference(resolution, [status(thm)], [c_42, c_82688])).
% 17.07/10.21  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 17.07/10.21  tff(c_233, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 17.07/10.21  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 17.07/10.21  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 17.07/10.21  tff(c_2938, plain, (![B_147, A_148]: (v4_pre_topc(B_147, A_148) | k2_pre_topc(A_148, B_147)!=B_147 | ~v2_pre_topc(A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.07/10.21  tff(c_2944, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2938])).
% 17.07/10.21  tff(c_2956, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_2944])).
% 17.07/10.21  tff(c_2957, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_233, c_2956])).
% 17.07/10.21  tff(c_3216, plain, (![A_153, B_154]: (k4_subset_1(u1_struct_0(A_153), B_154, k2_tops_1(A_153, B_154))=k2_pre_topc(A_153, B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_112])).
% 17.07/10.21  tff(c_3220, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_3216])).
% 17.07/10.21  tff(c_3230, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3220])).
% 17.07/10.21  tff(c_1233, plain, (![A_102, B_103, C_104]: (k7_subset_1(A_102, B_103, C_104)=k4_xboole_0(B_103, C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.07/10.21  tff(c_1270, plain, (![C_109]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_109)=k4_xboole_0('#skF_2', C_109))), inference(resolution, [status(thm)], [c_42, c_1233])).
% 17.07/10.21  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 17.07/10.21  tff(c_389, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_233, c_54])).
% 17.07/10.21  tff(c_1276, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1270, c_389])).
% 17.07/10.21  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.07/10.21  tff(c_90, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.07/10.21  tff(c_98, plain, (![A_4, B_5]: (k2_xboole_0(k4_xboole_0(A_4, B_5), A_4)=A_4)), inference(resolution, [status(thm)], [c_6, c_90])).
% 17.07/10.21  tff(c_1306, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1276, c_98])).
% 17.07/10.21  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.07/10.21  tff(c_118, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), A_53)=A_53)), inference(resolution, [status(thm)], [c_6, c_90])).
% 17.07/10.21  tff(c_125, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_4])).
% 17.07/10.21  tff(c_165, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.07/10.21  tff(c_174, plain, (![B_54]: (k5_xboole_0(B_54, k1_xboole_0)=k2_xboole_0(B_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_125, c_165])).
% 17.07/10.21  tff(c_180, plain, (![B_54]: (k5_xboole_0(B_54, k1_xboole_0)=B_54)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_174])).
% 17.07/10.21  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.07/10.21  tff(c_26, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.07/10.21  tff(c_219, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.07/10.21  tff(c_225, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=k3_subset_1(A_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_219])).
% 17.07/10.21  tff(c_231, plain, (![A_24]: (k3_subset_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_225])).
% 17.07/10.21  tff(c_316, plain, (![A_66, B_67]: (k3_subset_1(A_66, k3_subset_1(A_66, B_67))=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.07/10.21  tff(c_320, plain, (![A_24]: (k3_subset_1(A_24, k3_subset_1(A_24, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_316])).
% 17.07/10.21  tff(c_325, plain, (![A_24]: (k3_subset_1(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_320])).
% 17.07/10.21  tff(c_14, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.07/10.21  tff(c_18, plain, (![A_15]: (m1_subset_1(k2_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.07/10.21  tff(c_55, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 17.07/10.21  tff(c_232, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_subset_1(A_15, A_15))), inference(resolution, [status(thm)], [c_55, c_219])).
% 17.07/10.21  tff(c_329, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_325, c_232])).
% 17.07/10.21  tff(c_456, plain, (![A_73, B_74, C_75]: (k4_xboole_0(k4_xboole_0(A_73, B_74), C_75)=k4_xboole_0(A_73, k2_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.07/10.21  tff(c_488, plain, (![A_15, C_75]: (k4_xboole_0(A_15, k2_xboole_0(A_15, C_75))=k4_xboole_0(k1_xboole_0, C_75))), inference(superposition, [status(thm), theory('equality')], [c_329, c_456])).
% 17.07/10.21  tff(c_512, plain, (![A_76, C_77]: (k4_xboole_0(A_76, k2_xboole_0(A_76, C_77))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_488])).
% 17.07/10.21  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.07/10.21  tff(c_524, plain, (![A_76, C_77]: (k5_xboole_0(k2_xboole_0(A_76, C_77), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_76, C_77), A_76))), inference(superposition, [status(thm), theory('equality')], [c_512, c_12])).
% 17.07/10.21  tff(c_557, plain, (![A_76, C_77]: (k2_xboole_0(k2_xboole_0(A_76, C_77), A_76)=k2_xboole_0(A_76, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_524])).
% 17.07/10.21  tff(c_1326, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_557])).
% 17.07/10.21  tff(c_1335, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1326])).
% 17.07/10.21  tff(c_34, plain, (![A_31, B_32]: (m1_subset_1(k2_tops_1(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 17.07/10.21  tff(c_2659, plain, (![A_134, B_135, C_136]: (k4_subset_1(A_134, B_135, C_136)=k2_xboole_0(B_135, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_134)) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.07/10.21  tff(c_29605, plain, (![A_351, B_352, B_353]: (k4_subset_1(u1_struct_0(A_351), B_352, k2_tops_1(A_351, B_353))=k2_xboole_0(B_352, k2_tops_1(A_351, B_353)) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351))), inference(resolution, [status(thm)], [c_34, c_2659])).
% 17.07/10.21  tff(c_29609, plain, (![B_353]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_353))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_353)) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_29605])).
% 17.07/10.21  tff(c_82240, plain, (![B_539]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_539))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_539)) | ~m1_subset_1(B_539, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_29609])).
% 17.07/10.21  tff(c_82247, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_82240])).
% 17.07/10.21  tff(c_82260, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3230, c_1335, c_82247])).
% 17.07/10.21  tff(c_82262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2957, c_82260])).
% 17.07/10.21  tff(c_82263, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 17.07/10.21  tff(c_82708, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82695, c_82263])).
% 17.07/10.21  tff(c_82264, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 17.07/10.21  tff(c_82974, plain, (![A_579, B_580]: (k2_pre_topc(A_579, B_580)=B_580 | ~v4_pre_topc(B_580, A_579) | ~m1_subset_1(B_580, k1_zfmisc_1(u1_struct_0(A_579))) | ~l1_pre_topc(A_579))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.07/10.21  tff(c_82977, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_82974])).
% 17.07/10.21  tff(c_82988, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_82264, c_82977])).
% 17.07/10.21  tff(c_86835, plain, (![A_658, B_659]: (k7_subset_1(u1_struct_0(A_658), k2_pre_topc(A_658, B_659), k1_tops_1(A_658, B_659))=k2_tops_1(A_658, B_659) | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0(A_658))) | ~l1_pre_topc(A_658))), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.07/10.21  tff(c_86844, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_82988, c_86835])).
% 17.07/10.21  tff(c_86848, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_82695, c_86844])).
% 17.07/10.21  tff(c_86850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82708, c_86848])).
% 17.07/10.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.07/10.21  
% 17.07/10.21  Inference rules
% 17.07/10.21  ----------------------
% 17.07/10.21  #Ref     : 0
% 17.07/10.21  #Sup     : 21420
% 17.07/10.21  #Fact    : 0
% 17.07/10.21  #Define  : 0
% 17.07/10.21  #Split   : 2
% 17.07/10.21  #Chain   : 0
% 17.07/10.21  #Close   : 0
% 17.07/10.21  
% 17.07/10.21  Ordering : KBO
% 17.07/10.21  
% 17.07/10.21  Simplification rules
% 17.07/10.21  ----------------------
% 17.07/10.21  #Subsume      : 1
% 17.07/10.21  #Demod        : 27312
% 17.07/10.21  #Tautology    : 16556
% 17.07/10.21  #SimpNegUnit  : 4
% 17.07/10.21  #BackRed      : 15
% 17.07/10.21  
% 17.07/10.21  #Partial instantiations: 0
% 17.07/10.21  #Strategies tried      : 1
% 17.07/10.21  
% 17.07/10.21  Timing (in seconds)
% 17.07/10.21  ----------------------
% 17.07/10.22  Preprocessing        : 0.32
% 17.07/10.22  Parsing              : 0.17
% 17.07/10.22  CNF conversion       : 0.02
% 17.07/10.22  Main loop            : 9.14
% 17.07/10.22  Inferencing          : 1.26
% 17.07/10.22  Reduction            : 5.64
% 17.07/10.22  Demodulation         : 5.15
% 17.07/10.22  BG Simplification    : 0.12
% 17.07/10.22  Subsumption          : 1.79
% 17.07/10.22  Abstraction          : 0.26
% 17.07/10.22  MUC search           : 0.00
% 17.07/10.22  Cooper               : 0.00
% 17.07/10.22  Total                : 9.50
% 17.07/10.22  Index Insertion      : 0.00
% 17.07/10.22  Index Deletion       : 0.00
% 17.07/10.22  Index Matching       : 0.00
% 17.07/10.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
