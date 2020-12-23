%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1261+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:40 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 252 expanded)
%              Number of equality atoms :   48 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_99,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_97,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_116,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_23174,plain,(
    ! [A_402,B_403,C_404] :
      ( k7_subset_1(A_402,B_403,C_404) = k4_xboole_0(B_403,C_404)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(A_402)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_23180,plain,(
    ! [C_404] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_404) = k4_xboole_0('#skF_3',C_404) ),
    inference(resolution,[status(thm)],[c_42,c_23174])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_116,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4437,plain,(
    ! [B_189,A_190] :
      ( v4_pre_topc(B_189,A_190)
      | k2_pre_topc(A_190,B_189) != B_189
      | ~ v2_pre_topc(A_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4470,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_4437])).

tff(c_4496,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_4470])).

tff(c_4497,plain,(
    k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_4496])).

tff(c_135,plain,(
    ! [A_65,B_66,C_67] :
      ( k7_subset_1(A_65,B_66,C_67) = k4_xboole_0(B_66,C_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_144,plain,(
    ! [C_67] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_67) = k4_xboole_0('#skF_3',C_67) ),
    inference(resolution,[status(thm)],[c_42,c_135])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_176,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_54])).

tff(c_177,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_176])).

tff(c_30,plain,(
    ! [A_35] : k4_xboole_0(A_35,k1_xboole_0) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_34] : k3_xboole_0(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_233,plain,(
    ! [A_79,B_80,C_81] : k2_xboole_0(k4_xboole_0(A_79,B_80),k4_xboole_0(A_79,C_81)) = k4_xboole_0(A_79,k3_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_263,plain,(
    ! [A_35,B_80] : k4_xboole_0(A_35,k3_xboole_0(B_80,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_35,B_80),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_233])).

tff(c_268,plain,(
    ! [A_82,B_83] : k2_xboole_0(k4_xboole_0(A_82,B_83),A_82) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_263])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_xboole_0(B_5,A_4) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_274,plain,(
    ! [A_82,B_83] : k2_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_4])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k7_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1778,plain,(
    ! [A_143,B_144,C_145] :
      ( k4_subset_1(A_143,B_144,C_145) = k2_xboole_0(B_144,C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(A_143))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_21714,plain,(
    ! [A_382,B_383,B_384,C_385] :
      ( k4_subset_1(A_382,B_383,k7_subset_1(A_382,B_384,C_385)) = k2_xboole_0(B_383,k7_subset_1(A_382,B_384,C_385))
      | ~ m1_subset_1(B_383,k1_zfmisc_1(A_382))
      | ~ m1_subset_1(B_384,k1_zfmisc_1(A_382)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1778])).

tff(c_22952,plain,(
    ! [B_393,C_394] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k7_subset_1(u1_struct_0('#skF_2'),B_393,C_394)) = k2_xboole_0('#skF_3',k7_subset_1(u1_struct_0('#skF_2'),B_393,C_394))
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_21714])).

tff(c_22987,plain,(
    ! [C_67] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k4_xboole_0('#skF_3',C_67)) = k2_xboole_0('#skF_3',k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_67))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_22952])).

tff(c_23006,plain,(
    ! [C_395] : k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k4_xboole_0('#skF_3',C_395)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_274,c_144,c_22987])).

tff(c_23122,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_23006])).

tff(c_5099,plain,(
    ! [A_196,B_197] :
      ( k4_subset_1(u1_struct_0(A_196),B_197,k2_tops_1(A_196,B_197)) = k2_pre_topc(A_196,B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5124,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_5099])).

tff(c_5152,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5124])).

tff(c_23159,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23122,c_5152])).

tff(c_23161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4497,c_23159])).

tff(c_23162,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_23184,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23180,c_23162])).

tff(c_23163,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_23646,plain,(
    ! [A_443,B_444] :
      ( k2_pre_topc(A_443,B_444) = B_444
      | ~ v4_pre_topc(B_444,A_443)
      | ~ m1_subset_1(B_444,k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ l1_pre_topc(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_23663,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_23646])).

tff(c_23678,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_23163,c_23663])).

tff(c_30848,plain,(
    ! [A_575,B_576] :
      ( k7_subset_1(u1_struct_0(A_575),k2_pre_topc(A_575,B_576),k1_tops_1(A_575,B_576)) = k2_tops_1(A_575,B_576)
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ l1_pre_topc(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30872,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23678,c_30848])).

tff(c_30882,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_23180,c_30872])).

tff(c_30884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23184,c_30882])).

%------------------------------------------------------------------------------
