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
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 153 expanded)
%              Number of leaves         :   48 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 ( 235 expanded)
%              Number of equality atoms :   55 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_98,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_144,axiom,(
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

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_188,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_173])).

tff(c_191,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_188])).

tff(c_36,plain,(
    ! [B_26] : k4_xboole_0(k1_tarski(B_26),k1_tarski(B_26)) != k1_tarski(B_26) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_192,plain,(
    ! [B_26] : k1_tarski(B_26) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_36])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_29] : r1_tarski(k1_tarski(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_389,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(k2_xboole_0(A_97,B_98),B_98) = A_97
      | ~ r1_xboole_0(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,k4_xboole_0(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_457,plain,(
    ! [A_104,A_105,B_106] :
      ( r1_xboole_0(A_104,A_105)
      | ~ r1_tarski(A_104,B_106)
      | ~ r1_xboole_0(A_105,B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_20])).

tff(c_567,plain,(
    ! [A_127,A_128] :
      ( r1_xboole_0(k1_tarski(A_127),A_128)
      | ~ r1_xboole_0(A_128,k1_zfmisc_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_42,c_457])).

tff(c_584,plain,(
    ! [A_127,A_27] :
      ( r1_xboole_0(k1_tarski(A_127),k1_tarski(A_27))
      | r2_hidden(A_27,k1_zfmisc_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_40,c_567])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_683,plain,(
    ! [C_151,B_152,D_153,A_154] :
      ( C_151 = B_152
      | ~ r1_xboole_0(D_153,B_152)
      | ~ r1_xboole_0(C_151,A_154)
      | k2_xboole_0(C_151,D_153) != k2_xboole_0(A_154,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_709,plain,(
    ! [C_151,A_154,A_8] :
      ( k1_xboole_0 = C_151
      | ~ r1_xboole_0(C_151,A_154)
      | k2_xboole_0(C_151,A_8) != k2_xboole_0(A_154,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_683])).

tff(c_726,plain,(
    ! [C_155,A_156,A_157] :
      ( k1_xboole_0 = C_155
      | ~ r1_xboole_0(C_155,A_156)
      | k2_xboole_0(C_155,A_157) != A_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_709])).

tff(c_738,plain,(
    ! [A_127,A_157,A_27] :
      ( k1_tarski(A_127) = k1_xboole_0
      | k2_xboole_0(k1_tarski(A_127),A_157) != k1_tarski(A_27)
      | r2_hidden(A_27,k1_zfmisc_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_584,c_726])).

tff(c_1251,plain,(
    ! [A_221,A_222,A_223] :
      ( k2_xboole_0(k1_tarski(A_221),A_222) != k1_tarski(A_223)
      | r2_hidden(A_223,k1_zfmisc_1(A_221)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_738])).

tff(c_1255,plain,(
    ! [A_225,A_224] :
      ( k1_tarski(A_225) != k1_tarski(A_224)
      | r2_hidden(A_224,k1_zfmisc_1(A_225)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1251])).

tff(c_50,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1280,plain,(
    ! [A_229,A_230] :
      ( m1_subset_1(A_229,k1_zfmisc_1(A_230))
      | k1_tarski(A_230) != k1_tarski(A_229) ) ),
    inference(resolution,[status(thm)],[c_1255,c_50])).

tff(c_68,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_442,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(A_101,B_102) = k3_subset_1(A_101,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_445,plain,(
    ! [A_34] : k4_xboole_0(A_34,k1_xboole_0) = k3_subset_1(A_34,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_442])).

tff(c_447,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_xboole_0) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_445])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_135,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_141,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_60,c_135])).

tff(c_145,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_141])).

tff(c_613,plain,(
    ! [B_134,A_135] :
      ( v4_pre_topc(B_134,A_135)
      | ~ v1_xboole_0(B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_616,plain,(
    ! [B_134] :
      ( v4_pre_topc(B_134,'#skF_1')
      | ~ v1_xboole_0(B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_613])).

tff(c_641,plain,(
    ! [B_141] :
      ( v4_pre_topc(B_141,'#skF_1')
      | ~ v1_xboole_0(B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_616])).

tff(c_645,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_641])).

tff(c_648,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_645])).

tff(c_796,plain,(
    ! [A_163,B_164] :
      ( k2_pre_topc(A_163,B_164) = B_164
      | ~ v4_pre_topc(B_164,A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_904,plain,(
    ! [A_185] :
      ( k2_pre_topc(A_185,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_185)
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_48,c_796])).

tff(c_907,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_648,c_904])).

tff(c_913,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_907])).

tff(c_493,plain,(
    ! [A_115,B_116] :
      ( k3_subset_1(A_115,k3_subset_1(A_115,B_116)) = B_116
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_495,plain,(
    ! [A_34] : k3_subset_1(A_34,k3_subset_1(A_34,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_493])).

tff(c_497,plain,(
    ! [A_34] : k3_subset_1(A_34,A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_495])).

tff(c_947,plain,(
    ! [A_191,B_192] :
      ( k3_subset_1(u1_struct_0(A_191),k2_pre_topc(A_191,k3_subset_1(u1_struct_0(A_191),B_192))) = k1_tops_1(A_191,B_192)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_973,plain,(
    ! [B_192] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_192))) = k1_tops_1('#skF_1',B_192)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_947])).

tff(c_1201,plain,(
    ! [B_217] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_217))) = k1_tops_1('#skF_1',B_217)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_145,c_145,c_973])).

tff(c_1217,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_1201])).

tff(c_1224,plain,
    ( k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_913,c_1217])).

tff(c_1225,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1224])).

tff(c_1316,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1280,c_1225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.63  
% 3.63/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.63  %$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.63/1.63  
% 3.63/1.63  %Foreground sorts:
% 3.63/1.63  
% 3.63/1.63  
% 3.63/1.63  %Background operators:
% 3.63/1.63  
% 3.63/1.63  
% 3.63/1.63  %Foreground operators:
% 3.63/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.63/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.63/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.63/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.63/1.63  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.63/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.63/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.63/1.63  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.63/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.63/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.63/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.63/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.63  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.63/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.63/1.63  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.63/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.63/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.63  
% 3.63/1.65  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.63/1.65  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.63/1.65  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.63/1.65  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.63/1.65  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.63/1.65  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 3.63/1.65  tff(f_88, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 3.63/1.65  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.63/1.65  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.63/1.65  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.63/1.65  tff(f_56, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 3.63/1.65  tff(f_102, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.63/1.65  tff(f_158, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.63/1.65  tff(f_98, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.63/1.65  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.63/1.65  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.63/1.65  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.63/1.65  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.63/1.65  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.63/1.65  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.63/1.65  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.63/1.65  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.63/1.65  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.63/1.65  tff(c_8, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.63/1.65  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.63/1.65  tff(c_173, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.63/1.65  tff(c_188, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_173])).
% 3.63/1.65  tff(c_191, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_188])).
% 3.63/1.65  tff(c_36, plain, (![B_26]: (k4_xboole_0(k1_tarski(B_26), k1_tarski(B_26))!=k1_tarski(B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.63/1.65  tff(c_192, plain, (![B_26]: (k1_tarski(B_26)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_191, c_36])).
% 3.63/1.65  tff(c_40, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.63/1.65  tff(c_42, plain, (![A_29]: (r1_tarski(k1_tarski(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.76/1.65  tff(c_389, plain, (![A_97, B_98]: (k4_xboole_0(k2_xboole_0(A_97, B_98), B_98)=A_97 | ~r1_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.76/1.65  tff(c_20, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, k4_xboole_0(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.76/1.65  tff(c_457, plain, (![A_104, A_105, B_106]: (r1_xboole_0(A_104, A_105) | ~r1_tarski(A_104, B_106) | ~r1_xboole_0(A_105, B_106))), inference(superposition, [status(thm), theory('equality')], [c_389, c_20])).
% 3.76/1.65  tff(c_567, plain, (![A_127, A_128]: (r1_xboole_0(k1_tarski(A_127), A_128) | ~r1_xboole_0(A_128, k1_zfmisc_1(A_127)))), inference(resolution, [status(thm)], [c_42, c_457])).
% 3.76/1.65  tff(c_584, plain, (![A_127, A_27]: (r1_xboole_0(k1_tarski(A_127), k1_tarski(A_27)) | r2_hidden(A_27, k1_zfmisc_1(A_127)))), inference(resolution, [status(thm)], [c_40, c_567])).
% 3.76/1.65  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.76/1.65  tff(c_683, plain, (![C_151, B_152, D_153, A_154]: (C_151=B_152 | ~r1_xboole_0(D_153, B_152) | ~r1_xboole_0(C_151, A_154) | k2_xboole_0(C_151, D_153)!=k2_xboole_0(A_154, B_152))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.76/1.65  tff(c_709, plain, (![C_151, A_154, A_8]: (k1_xboole_0=C_151 | ~r1_xboole_0(C_151, A_154) | k2_xboole_0(C_151, A_8)!=k2_xboole_0(A_154, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_683])).
% 3.76/1.65  tff(c_726, plain, (![C_155, A_156, A_157]: (k1_xboole_0=C_155 | ~r1_xboole_0(C_155, A_156) | k2_xboole_0(C_155, A_157)!=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_709])).
% 3.76/1.65  tff(c_738, plain, (![A_127, A_157, A_27]: (k1_tarski(A_127)=k1_xboole_0 | k2_xboole_0(k1_tarski(A_127), A_157)!=k1_tarski(A_27) | r2_hidden(A_27, k1_zfmisc_1(A_127)))), inference(resolution, [status(thm)], [c_584, c_726])).
% 3.76/1.65  tff(c_1251, plain, (![A_221, A_222, A_223]: (k2_xboole_0(k1_tarski(A_221), A_222)!=k1_tarski(A_223) | r2_hidden(A_223, k1_zfmisc_1(A_221)))), inference(negUnitSimplification, [status(thm)], [c_192, c_738])).
% 3.76/1.65  tff(c_1255, plain, (![A_225, A_224]: (k1_tarski(A_225)!=k1_tarski(A_224) | r2_hidden(A_224, k1_zfmisc_1(A_225)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1251])).
% 3.76/1.65  tff(c_50, plain, (![A_35, B_36]: (m1_subset_1(A_35, B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.76/1.65  tff(c_1280, plain, (![A_229, A_230]: (m1_subset_1(A_229, k1_zfmisc_1(A_230)) | k1_tarski(A_230)!=k1_tarski(A_229))), inference(resolution, [status(thm)], [c_1255, c_50])).
% 3.76/1.65  tff(c_68, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.76/1.65  tff(c_48, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.76/1.65  tff(c_442, plain, (![A_101, B_102]: (k4_xboole_0(A_101, B_102)=k3_subset_1(A_101, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.76/1.65  tff(c_445, plain, (![A_34]: (k4_xboole_0(A_34, k1_xboole_0)=k3_subset_1(A_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_442])).
% 3.76/1.65  tff(c_447, plain, (![A_34]: (k3_subset_1(A_34, k1_xboole_0)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_445])).
% 3.76/1.65  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.76/1.65  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.76/1.65  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.76/1.65  tff(c_60, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.76/1.65  tff(c_135, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.76/1.65  tff(c_141, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_60, c_135])).
% 3.76/1.65  tff(c_145, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_141])).
% 3.76/1.65  tff(c_613, plain, (![B_134, A_135]: (v4_pre_topc(B_134, A_135) | ~v1_xboole_0(B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.76/1.65  tff(c_616, plain, (![B_134]: (v4_pre_topc(B_134, '#skF_1') | ~v1_xboole_0(B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_613])).
% 3.76/1.65  tff(c_641, plain, (![B_141]: (v4_pre_topc(B_141, '#skF_1') | ~v1_xboole_0(B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_616])).
% 3.76/1.65  tff(c_645, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_641])).
% 3.76/1.65  tff(c_648, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_645])).
% 3.76/1.65  tff(c_796, plain, (![A_163, B_164]: (k2_pre_topc(A_163, B_164)=B_164 | ~v4_pre_topc(B_164, A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.76/1.65  tff(c_904, plain, (![A_185]: (k2_pre_topc(A_185, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_185) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_48, c_796])).
% 3.76/1.65  tff(c_907, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_648, c_904])).
% 3.76/1.65  tff(c_913, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_907])).
% 3.76/1.65  tff(c_493, plain, (![A_115, B_116]: (k3_subset_1(A_115, k3_subset_1(A_115, B_116))=B_116 | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.76/1.65  tff(c_495, plain, (![A_34]: (k3_subset_1(A_34, k3_subset_1(A_34, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_493])).
% 3.76/1.65  tff(c_497, plain, (![A_34]: (k3_subset_1(A_34, A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_447, c_495])).
% 3.76/1.65  tff(c_947, plain, (![A_191, B_192]: (k3_subset_1(u1_struct_0(A_191), k2_pre_topc(A_191, k3_subset_1(u1_struct_0(A_191), B_192)))=k1_tops_1(A_191, B_192) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.76/1.65  tff(c_973, plain, (![B_192]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_192)))=k1_tops_1('#skF_1', B_192) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_947])).
% 3.76/1.65  tff(c_1201, plain, (![B_217]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_217)))=k1_tops_1('#skF_1', B_217) | ~m1_subset_1(B_217, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_145, c_145, c_973])).
% 3.76/1.65  tff(c_1217, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_497, c_1201])).
% 3.76/1.65  tff(c_1224, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_913, c_1217])).
% 3.76/1.65  tff(c_1225, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1224])).
% 3.76/1.65  tff(c_1316, plain, $false, inference(resolution, [status(thm)], [c_1280, c_1225])).
% 3.76/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.65  
% 3.76/1.65  Inference rules
% 3.76/1.65  ----------------------
% 3.76/1.65  #Ref     : 7
% 3.76/1.65  #Sup     : 282
% 3.76/1.65  #Fact    : 0
% 3.76/1.65  #Define  : 0
% 3.76/1.65  #Split   : 0
% 3.76/1.65  #Chain   : 0
% 3.76/1.65  #Close   : 0
% 3.76/1.65  
% 3.76/1.65  Ordering : KBO
% 3.76/1.65  
% 3.76/1.65  Simplification rules
% 3.76/1.65  ----------------------
% 3.76/1.65  #Subsume      : 18
% 3.76/1.65  #Demod        : 110
% 3.76/1.65  #Tautology    : 121
% 3.76/1.65  #SimpNegUnit  : 18
% 3.76/1.65  #BackRed      : 3
% 3.76/1.65  
% 3.76/1.65  #Partial instantiations: 0
% 3.76/1.65  #Strategies tried      : 1
% 3.76/1.65  
% 3.76/1.65  Timing (in seconds)
% 3.76/1.65  ----------------------
% 3.76/1.65  Preprocessing        : 0.37
% 3.76/1.65  Parsing              : 0.21
% 3.76/1.65  CNF conversion       : 0.02
% 3.76/1.65  Main loop            : 0.44
% 3.76/1.65  Inferencing          : 0.16
% 3.76/1.65  Reduction            : 0.14
% 3.76/1.65  Demodulation         : 0.10
% 3.76/1.65  BG Simplification    : 0.03
% 3.76/1.65  Subsumption          : 0.08
% 3.76/1.65  Abstraction          : 0.03
% 3.76/1.65  MUC search           : 0.00
% 3.76/1.65  Cooper               : 0.00
% 3.76/1.65  Total                : 0.85
% 3.76/1.65  Index Insertion      : 0.00
% 3.76/1.65  Index Deletion       : 0.00
% 3.76/1.65  Index Matching       : 0.00
% 3.76/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
