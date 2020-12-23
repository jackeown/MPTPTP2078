%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 234 expanded)
%              Number of leaves         :   47 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  147 ( 399 expanded)
%              Number of equality atoms :   40 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_54,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_125,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_56,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_34] : m1_subset_1(k2_subset_1(A_34),k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [A_34] : m1_subset_1(A_34,k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    ! [A_52] :
      ( l1_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    ! [A_53] :
      ( v1_xboole_0(k1_struct_0(A_53))
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82,plain,(
    ! [B_67,A_68] :
      ( ~ v1_xboole_0(B_67)
      | B_67 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [A_69] :
      ( k1_xboole_0 = A_69
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_99,plain,(
    ! [A_70] :
      ( k1_struct_0(A_70) = k1_xboole_0
      | ~ l1_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_104,plain,(
    ! [A_71] :
      ( k1_struct_0(A_71) = k1_xboole_0
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_108,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_104])).

tff(c_117,plain,(
    ! [A_72] :
      ( u1_struct_0(A_72) = k2_struct_0(A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_122,plain,(
    ! [A_73] :
      ( u1_struct_0(A_73) = k2_struct_0(A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_44,c_117])).

tff(c_126,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_234,plain,(
    ! [A_91] :
      ( k3_subset_1(u1_struct_0(A_91),k1_struct_0(A_91)) = k2_struct_0(A_91)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_243,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_234])).

tff(c_249,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_243])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_271])).

tff(c_276,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    ! [A_39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_409,plain,(
    ! [B_128,A_129] :
      ( v4_pre_topc(B_128,A_129)
      | ~ v1_xboole_0(B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_427,plain,(
    ! [A_129] :
      ( v4_pre_topc(k1_xboole_0,A_129)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_28,c_409])).

tff(c_436,plain,(
    ! [A_130] :
      ( v4_pre_topc(k1_xboole_0,A_130)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_427])).

tff(c_365,plain,(
    ! [A_124,B_125] :
      ( k2_pre_topc(A_124,B_125) = B_125
      | ~ v4_pre_topc(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_375,plain,(
    ! [B_125] :
      ( k2_pre_topc('#skF_1',B_125) = B_125
      | ~ v4_pre_topc(B_125,'#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_365])).

tff(c_390,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_1',B_126) = B_126
      | ~ v4_pre_topc(B_126,'#skF_1')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_375])).

tff(c_405,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_390])).

tff(c_406,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_442,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_436,c_406])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_442])).

tff(c_448,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_142,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_153,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_61,c_142])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_745,plain,(
    ! [A_170,C_171,B_172] :
      ( r1_tarski(k3_subset_1(A_170,C_171),B_172)
      | ~ r1_tarski(k3_subset_1(A_170,B_172),C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(A_170))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_747,plain,(
    ! [C_171] :
      ( r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),C_171),k1_xboole_0)
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_745])).

tff(c_756,plain,(
    ! [C_173] :
      ( r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),C_173),k1_xboole_0)
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_747])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_761,plain,(
    ! [C_173] :
      ( k3_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),C_173),k1_xboole_0) = k3_subset_1(k2_struct_0('#skF_1'),C_173)
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_756,c_4])).

tff(c_772,plain,(
    ! [C_174] :
      ( k3_subset_1(k2_struct_0('#skF_1'),C_174) = k1_xboole_0
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_761])).

tff(c_780,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0
    | ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_61,c_772])).

tff(c_788,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_780])).

tff(c_805,plain,(
    ! [A_175,B_176] :
      ( k3_subset_1(u1_struct_0(A_175),k2_pre_topc(A_175,k3_subset_1(u1_struct_0(A_175),B_176))) = k1_tops_1(A_175,B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_825,plain,(
    ! [B_176] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_176))) = k1_tops_1('#skF_1',B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_805])).

tff(c_892,plain,(
    ! [B_180] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_180))) = k1_tops_1('#skF_1',B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_126,c_126,c_825])).

tff(c_918,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_892])).

tff(c_925,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_276,c_448,c_918])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.18/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.18/1.49  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.18/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.18/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.18/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.18/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.18/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.18/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.18/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.18/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.18/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.18/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.18/1.49  
% 3.18/1.51  tff(f_139, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.18/1.51  tff(f_54, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.18/1.51  tff(f_56, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.18/1.51  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.18/1.51  tff(f_106, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 3.18/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.18/1.51  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.18/1.51  tff(f_94, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.18/1.51  tff(f_110, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 3.18/1.51  tff(f_67, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.18/1.51  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.18/1.51  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.18/1.51  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.18/1.51  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.18/1.51  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 3.18/1.51  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.18/1.51  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.18/1.51  tff(c_56, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.18/1.51  tff(c_22, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.18/1.51  tff(c_24, plain, (![A_34]: (m1_subset_1(k2_subset_1(A_34), k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.51  tff(c_61, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.18/1.51  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.18/1.51  tff(c_44, plain, (![A_52]: (l1_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.18/1.51  tff(c_46, plain, (![A_53]: (v1_xboole_0(k1_struct_0(A_53)) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.18/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.18/1.51  tff(c_82, plain, (![B_67, A_68]: (~v1_xboole_0(B_67) | B_67=A_68 | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.51  tff(c_89, plain, (![A_69]: (k1_xboole_0=A_69 | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_2, c_82])).
% 3.18/1.51  tff(c_99, plain, (![A_70]: (k1_struct_0(A_70)=k1_xboole_0 | ~l1_struct_0(A_70))), inference(resolution, [status(thm)], [c_46, c_89])).
% 3.18/1.51  tff(c_104, plain, (![A_71]: (k1_struct_0(A_71)=k1_xboole_0 | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_44, c_99])).
% 3.18/1.51  tff(c_108, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_104])).
% 3.18/1.51  tff(c_117, plain, (![A_72]: (u1_struct_0(A_72)=k2_struct_0(A_72) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.18/1.51  tff(c_122, plain, (![A_73]: (u1_struct_0(A_73)=k2_struct_0(A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_44, c_117])).
% 3.18/1.51  tff(c_126, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_122])).
% 3.18/1.51  tff(c_234, plain, (![A_91]: (k3_subset_1(u1_struct_0(A_91), k1_struct_0(A_91))=k2_struct_0(A_91) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.51  tff(c_243, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_126, c_234])).
% 3.18/1.51  tff(c_249, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_243])).
% 3.18/1.51  tff(c_268, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_249])).
% 3.18/1.51  tff(c_271, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_268])).
% 3.18/1.51  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_271])).
% 3.18/1.51  tff(c_276, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_249])).
% 3.18/1.51  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.18/1.51  tff(c_28, plain, (![A_39]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.51  tff(c_409, plain, (![B_128, A_129]: (v4_pre_topc(B_128, A_129) | ~v1_xboole_0(B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.18/1.51  tff(c_427, plain, (![A_129]: (v4_pre_topc(k1_xboole_0, A_129) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(resolution, [status(thm)], [c_28, c_409])).
% 3.18/1.51  tff(c_436, plain, (![A_130]: (v4_pre_topc(k1_xboole_0, A_130) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_427])).
% 3.18/1.51  tff(c_365, plain, (![A_124, B_125]: (k2_pre_topc(A_124, B_125)=B_125 | ~v4_pre_topc(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.18/1.51  tff(c_375, plain, (![B_125]: (k2_pre_topc('#skF_1', B_125)=B_125 | ~v4_pre_topc(B_125, '#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_365])).
% 3.18/1.51  tff(c_390, plain, (![B_126]: (k2_pre_topc('#skF_1', B_126)=B_126 | ~v4_pre_topc(B_126, '#skF_1') | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_375])).
% 3.18/1.51  tff(c_405, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_28, c_390])).
% 3.18/1.51  tff(c_406, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_405])).
% 3.18/1.51  tff(c_442, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_436, c_406])).
% 3.18/1.51  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_442])).
% 3.18/1.51  tff(c_448, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_405])).
% 3.18/1.51  tff(c_142, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.51  tff(c_153, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_61, c_142])).
% 3.18/1.51  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.51  tff(c_745, plain, (![A_170, C_171, B_172]: (r1_tarski(k3_subset_1(A_170, C_171), B_172) | ~r1_tarski(k3_subset_1(A_170, B_172), C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(A_170)) | ~m1_subset_1(B_172, k1_zfmisc_1(A_170)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.51  tff(c_747, plain, (![C_171]: (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), C_171), k1_xboole_0) | ~r1_tarski(k2_struct_0('#skF_1'), C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_276, c_745])).
% 3.18/1.51  tff(c_756, plain, (![C_173]: (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), C_173), k1_xboole_0) | ~r1_tarski(k2_struct_0('#skF_1'), C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_747])).
% 3.18/1.51  tff(c_4, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.18/1.51  tff(c_761, plain, (![C_173]: (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_1'), C_173), k1_xboole_0)=k3_subset_1(k2_struct_0('#skF_1'), C_173) | ~r1_tarski(k2_struct_0('#skF_1'), C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_756, c_4])).
% 3.18/1.51  tff(c_772, plain, (![C_174]: (k3_subset_1(k2_struct_0('#skF_1'), C_174)=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_1'), C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_761])).
% 3.18/1.51  tff(c_780, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_61, c_772])).
% 3.18/1.51  tff(c_788, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_153, c_780])).
% 3.18/1.51  tff(c_805, plain, (![A_175, B_176]: (k3_subset_1(u1_struct_0(A_175), k2_pre_topc(A_175, k3_subset_1(u1_struct_0(A_175), B_176)))=k1_tops_1(A_175, B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.18/1.51  tff(c_825, plain, (![B_176]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_176)))=k1_tops_1('#skF_1', B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_805])).
% 3.18/1.51  tff(c_892, plain, (![B_180]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_180)))=k1_tops_1('#skF_1', B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_126, c_126, c_825])).
% 3.18/1.51  tff(c_918, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_788, c_892])).
% 3.18/1.51  tff(c_925, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_276, c_448, c_918])).
% 3.18/1.51  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_925])).
% 3.18/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  Inference rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Ref     : 0
% 3.18/1.51  #Sup     : 179
% 3.18/1.51  #Fact    : 0
% 3.18/1.51  #Define  : 0
% 3.18/1.51  #Split   : 5
% 3.18/1.51  #Chain   : 0
% 3.18/1.51  #Close   : 0
% 3.18/1.51  
% 3.18/1.51  Ordering : KBO
% 3.18/1.51  
% 3.18/1.51  Simplification rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Subsume      : 27
% 3.18/1.51  #Demod        : 108
% 3.18/1.51  #Tautology    : 73
% 3.18/1.51  #SimpNegUnit  : 8
% 3.18/1.51  #BackRed      : 0
% 3.18/1.51  
% 3.18/1.51  #Partial instantiations: 0
% 3.18/1.51  #Strategies tried      : 1
% 3.18/1.51  
% 3.18/1.51  Timing (in seconds)
% 3.18/1.51  ----------------------
% 3.18/1.51  Preprocessing        : 0.33
% 3.18/1.51  Parsing              : 0.18
% 3.18/1.51  CNF conversion       : 0.02
% 3.18/1.51  Main loop            : 0.36
% 3.18/1.51  Inferencing          : 0.14
% 3.18/1.51  Reduction            : 0.11
% 3.18/1.51  Demodulation         : 0.08
% 3.18/1.51  BG Simplification    : 0.02
% 3.18/1.51  Subsumption          : 0.06
% 3.18/1.51  Abstraction          : 0.02
% 3.18/1.51  MUC search           : 0.00
% 3.18/1.51  Cooper               : 0.00
% 3.18/1.51  Total                : 0.73
% 3.18/1.51  Index Insertion      : 0.00
% 3.18/1.51  Index Deletion       : 0.00
% 3.18/1.51  Index Matching       : 0.00
% 3.18/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
