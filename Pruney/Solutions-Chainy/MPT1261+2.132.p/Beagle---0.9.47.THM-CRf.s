%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 6.81s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 143 expanded)
%              Number of leaves         :   39 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 273 expanded)
%              Number of equality atoms :   61 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
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

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8589,plain,(
    ! [A_322,B_323,C_324] :
      ( k7_subset_1(A_322,B_323,C_324) = k4_xboole_0(B_323,C_324)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(A_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8596,plain,(
    ! [C_324] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_324) = k4_xboole_0('#skF_2',C_324) ),
    inference(resolution,[status(thm)],[c_52,c_8589])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_121,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_259,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2024,plain,(
    ! [B_151,A_152] :
      ( v4_pre_topc(B_151,A_152)
      | k2_pre_topc(A_152,B_151) != B_151
      | ~ v2_pre_topc(A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2030,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2024])).

tff(c_2042,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_2030])).

tff(c_2043,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_2042])).

tff(c_2482,plain,(
    ! [A_159,B_160] :
      ( k4_subset_1(u1_struct_0(A_159),B_160,k2_tops_1(A_159,B_160)) = k2_pre_topc(A_159,B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2486,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2482])).

tff(c_2496,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2486])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_678,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(A_102,B_103,C_104) = k4_xboole_0(B_103,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_734,plain,(
    ! [C_110] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_110) = k4_xboole_0('#skF_2',C_110) ),
    inference(resolution,[status(thm)],[c_52,c_678])).

tff(c_746,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_734])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_20,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_199,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_199])).

tff(c_844,plain,(
    ! [A_115,B_116] : k3_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_211])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_850,plain,(
    ! [A_115,B_116] : k4_xboole_0(k4_xboole_0(A_115,B_116),k4_xboole_0(A_115,B_116)) = k4_xboole_0(k4_xboole_0(A_115,B_116),A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_183])).

tff(c_890,plain,(
    ! [A_115,B_116] : k4_xboole_0(k4_xboole_0(A_115,B_116),A_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_850])).

tff(c_1116,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_890])).

tff(c_18,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1145,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_18])).

tff(c_1152,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1145])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k2_tops_1(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1558,plain,(
    ! [A_141,B_142,C_143] :
      ( k4_subset_1(A_141,B_142,C_143) = k2_xboole_0(B_142,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(A_141))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7942,plain,(
    ! [A_270,B_271,B_272] :
      ( k4_subset_1(u1_struct_0(A_270),B_271,k2_tops_1(A_270,B_272)) = k2_xboole_0(B_271,k2_tops_1(A_270,B_272))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(resolution,[status(thm)],[c_44,c_1558])).

tff(c_7946,plain,(
    ! [B_272] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_272)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_272))
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_7942])).

tff(c_7959,plain,(
    ! [B_273] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_273)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_273))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7946])).

tff(c_7966,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_7959])).

tff(c_7979,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_1152,c_7966])).

tff(c_7981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2043,c_7979])).

tff(c_7982,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_7982])).

tff(c_8197,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8304,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8197,c_58])).

tff(c_8682,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_8304])).

tff(c_9104,plain,(
    ! [A_350,B_351] :
      ( k2_pre_topc(A_350,B_351) = B_351
      | ~ v4_pre_topc(B_351,A_350)
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ l1_pre_topc(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9107,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_9104])).

tff(c_9118,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8197,c_9107])).

tff(c_10614,plain,(
    ! [A_395,B_396] :
      ( k7_subset_1(u1_struct_0(A_395),k2_pre_topc(A_395,B_396),k1_tops_1(A_395,B_396)) = k2_tops_1(A_395,B_396)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_10623,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9118,c_10614])).

tff(c_10627,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_8596,c_10623])).

tff(c_10629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8682,c_10627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.81/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.69  
% 6.81/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.69  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.81/2.69  
% 6.81/2.69  %Foreground sorts:
% 6.81/2.69  
% 6.81/2.69  
% 6.81/2.69  %Background operators:
% 6.81/2.69  
% 6.81/2.69  
% 6.81/2.69  %Foreground operators:
% 6.81/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.81/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.81/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.81/2.69  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.81/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.81/2.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.81/2.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.81/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.81/2.69  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.81/2.69  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.81/2.69  tff('#skF_2', type, '#skF_2': $i).
% 6.81/2.69  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.81/2.69  tff('#skF_1', type, '#skF_1': $i).
% 6.81/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.81/2.69  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.81/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.81/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.81/2.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.81/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.81/2.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.81/2.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.81/2.69  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.81/2.69  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.81/2.69  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.81/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.81/2.69  
% 6.81/2.71  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.81/2.71  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.81/2.71  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.81/2.71  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.81/2.71  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.81/2.71  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.81/2.71  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.81/2.71  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.81/2.71  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.81/2.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.81/2.71  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.81/2.71  tff(f_98, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.81/2.71  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.81/2.71  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 6.81/2.71  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.81/2.71  tff(c_8589, plain, (![A_322, B_323, C_324]: (k7_subset_1(A_322, B_323, C_324)=k4_xboole_0(B_323, C_324) | ~m1_subset_1(B_323, k1_zfmisc_1(A_322)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.81/2.71  tff(c_8596, plain, (![C_324]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_324)=k4_xboole_0('#skF_2', C_324))), inference(resolution, [status(thm)], [c_52, c_8589])).
% 6.81/2.71  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.81/2.71  tff(c_121, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 6.81/2.71  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.81/2.71  tff(c_259, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 6.81/2.71  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.81/2.71  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.81/2.71  tff(c_2024, plain, (![B_151, A_152]: (v4_pre_topc(B_151, A_152) | k2_pre_topc(A_152, B_151)!=B_151 | ~v2_pre_topc(A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.81/2.71  tff(c_2030, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2024])).
% 6.81/2.71  tff(c_2042, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_2030])).
% 6.81/2.71  tff(c_2043, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_259, c_2042])).
% 6.81/2.71  tff(c_2482, plain, (![A_159, B_160]: (k4_subset_1(u1_struct_0(A_159), B_160, k2_tops_1(A_159, B_160))=k2_pre_topc(A_159, B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.81/2.71  tff(c_2486, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2482])).
% 6.81/2.71  tff(c_2496, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2486])).
% 6.81/2.71  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.81/2.71  tff(c_678, plain, (![A_102, B_103, C_104]: (k7_subset_1(A_102, B_103, C_104)=k4_xboole_0(B_103, C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.81/2.71  tff(c_734, plain, (![C_110]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_110)=k4_xboole_0('#skF_2', C_110))), inference(resolution, [status(thm)], [c_52, c_678])).
% 6.81/2.71  tff(c_746, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121, c_734])).
% 6.81/2.71  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.81/2.71  tff(c_123, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.81/2.71  tff(c_131, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_123])).
% 6.81/2.71  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.81/2.71  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.81/2.71  tff(c_199, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.81/2.71  tff(c_211, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_199])).
% 6.81/2.71  tff(c_844, plain, (![A_115, B_116]: (k3_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_211])).
% 6.81/2.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.81/2.71  tff(c_171, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.81/2.71  tff(c_183, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_171])).
% 6.81/2.71  tff(c_850, plain, (![A_115, B_116]: (k4_xboole_0(k4_xboole_0(A_115, B_116), k4_xboole_0(A_115, B_116))=k4_xboole_0(k4_xboole_0(A_115, B_116), A_115))), inference(superposition, [status(thm), theory('equality')], [c_844, c_183])).
% 6.81/2.71  tff(c_890, plain, (![A_115, B_116]: (k4_xboole_0(k4_xboole_0(A_115, B_116), A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_850])).
% 6.81/2.71  tff(c_1116, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_746, c_890])).
% 6.81/2.71  tff(c_18, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.81/2.71  tff(c_1145, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1116, c_18])).
% 6.81/2.71  tff(c_1152, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1145])).
% 6.81/2.71  tff(c_44, plain, (![A_37, B_38]: (m1_subset_1(k2_tops_1(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.81/2.71  tff(c_1558, plain, (![A_141, B_142, C_143]: (k4_subset_1(A_141, B_142, C_143)=k2_xboole_0(B_142, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(A_141)) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.81/2.71  tff(c_7942, plain, (![A_270, B_271, B_272]: (k4_subset_1(u1_struct_0(A_270), B_271, k2_tops_1(A_270, B_272))=k2_xboole_0(B_271, k2_tops_1(A_270, B_272)) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_270))) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(resolution, [status(thm)], [c_44, c_1558])).
% 6.81/2.71  tff(c_7946, plain, (![B_272]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_272))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_272)) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_7942])).
% 6.81/2.71  tff(c_7959, plain, (![B_273]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_273))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_273)) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7946])).
% 6.81/2.71  tff(c_7966, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_7959])).
% 6.81/2.71  tff(c_7979, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_1152, c_7966])).
% 6.81/2.71  tff(c_7981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2043, c_7979])).
% 6.81/2.71  tff(c_7982, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 6.81/2.71  tff(c_8196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_7982])).
% 6.81/2.71  tff(c_8197, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 6.81/2.71  tff(c_8304, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8197, c_58])).
% 6.81/2.71  tff(c_8682, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8596, c_8304])).
% 6.81/2.71  tff(c_9104, plain, (![A_350, B_351]: (k2_pre_topc(A_350, B_351)=B_351 | ~v4_pre_topc(B_351, A_350) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_350))) | ~l1_pre_topc(A_350))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.81/2.71  tff(c_9107, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_9104])).
% 6.81/2.71  tff(c_9118, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8197, c_9107])).
% 6.81/2.71  tff(c_10614, plain, (![A_395, B_396]: (k7_subset_1(u1_struct_0(A_395), k2_pre_topc(A_395, B_396), k1_tops_1(A_395, B_396))=k2_tops_1(A_395, B_396) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.81/2.71  tff(c_10623, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9118, c_10614])).
% 6.81/2.71  tff(c_10627, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_8596, c_10623])).
% 6.81/2.71  tff(c_10629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8682, c_10627])).
% 6.81/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.71  
% 6.81/2.71  Inference rules
% 6.81/2.71  ----------------------
% 6.81/2.71  #Ref     : 0
% 6.81/2.71  #Sup     : 2563
% 6.81/2.71  #Fact    : 0
% 6.81/2.71  #Define  : 0
% 6.81/2.71  #Split   : 5
% 6.81/2.71  #Chain   : 0
% 6.81/2.71  #Close   : 0
% 6.81/2.71  
% 6.81/2.71  Ordering : KBO
% 6.81/2.71  
% 6.81/2.71  Simplification rules
% 6.81/2.71  ----------------------
% 6.81/2.71  #Subsume      : 349
% 6.81/2.71  #Demod        : 3782
% 6.81/2.71  #Tautology    : 1959
% 6.81/2.71  #SimpNegUnit  : 6
% 6.81/2.71  #BackRed      : 11
% 6.81/2.71  
% 6.81/2.71  #Partial instantiations: 0
% 6.81/2.71  #Strategies tried      : 1
% 6.81/2.71  
% 6.81/2.71  Timing (in seconds)
% 6.81/2.71  ----------------------
% 6.81/2.71  Preprocessing        : 0.41
% 6.81/2.71  Parsing              : 0.21
% 6.81/2.71  CNF conversion       : 0.03
% 6.81/2.71  Main loop            : 1.43
% 6.81/2.71  Inferencing          : 0.38
% 6.81/2.71  Reduction            : 0.75
% 6.81/2.71  Demodulation         : 0.64
% 6.81/2.71  BG Simplification    : 0.04
% 6.81/2.71  Subsumption          : 0.19
% 6.81/2.71  Abstraction          : 0.07
% 6.81/2.71  MUC search           : 0.00
% 6.81/2.71  Cooper               : 0.00
% 6.81/2.71  Total                : 1.89
% 6.81/2.71  Index Insertion      : 0.00
% 6.81/2.71  Index Deletion       : 0.00
% 6.81/2.71  Index Matching       : 0.00
% 6.81/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
