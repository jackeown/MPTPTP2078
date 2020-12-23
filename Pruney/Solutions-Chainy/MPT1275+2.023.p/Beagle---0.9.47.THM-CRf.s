%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 149 expanded)
%              Number of leaves         :   49 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  141 ( 298 expanded)
%              Number of equality atoms :   39 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_90,axiom,(
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

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_66,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_107,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_308,plain,(
    ! [A_118,B_119] :
      ( k1_tops_1(A_118,B_119) = k1_xboole_0
      | ~ v2_tops_1(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_311,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_308])).

tff(c_318,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_311])).

tff(c_320,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_117,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_72])).

tff(c_378,plain,(
    ! [B_136,A_137] :
      ( v2_tops_1(B_136,A_137)
      | ~ r1_tarski(B_136,k2_tops_1(A_137,B_136))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_380,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_378])).

tff(c_385,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6,c_380])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_385])).

tff(c_389,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_60,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_475,plain,(
    ! [B_158,A_159] :
      ( v3_tops_1(B_158,A_159)
      | ~ v4_pre_topc(B_158,A_159)
      | ~ v2_tops_1(B_158,A_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_478,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_475])).

tff(c_485,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_389,c_60,c_478])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_485])).

tff(c_488,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_36,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_608,plain,(
    ! [A_190,B_191] :
      ( k1_subset_1(A_190) = B_191
      | ~ r1_tarski(B_191,k3_subset_1(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_615,plain,(
    ! [A_190] :
      ( k1_subset_1(A_190) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_190)) ) ),
    inference(resolution,[status(thm)],[c_10,c_608])).

tff(c_619,plain,(
    ! [A_190] : k1_subset_1(A_190) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_615])).

tff(c_24,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_39] : k3_subset_1(A_39,k1_subset_1(A_39)) = k2_subset_1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    ! [A_39] : k3_subset_1(A_39,k1_subset_1(A_39)) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_631,plain,(
    ! [A_39] : k3_subset_1(A_39,k1_xboole_0) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_74])).

tff(c_543,plain,(
    ! [A_171,B_172] :
      ( k4_xboole_0(A_171,B_172) = k3_subset_1(A_171,B_172)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_551,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_subset_1(A_42,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_543])).

tff(c_641,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_551])).

tff(c_574,plain,(
    ! [A_180,B_181,C_182] :
      ( k7_subset_1(A_180,B_181,C_182) = k4_xboole_0(B_181,C_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(A_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_579,plain,(
    ! [C_182] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_182) = k4_xboole_0('#skF_2',C_182) ),
    inference(resolution,[status(thm)],[c_62,c_574])).

tff(c_688,plain,(
    ! [A_205,B_206] :
      ( k2_pre_topc(A_205,B_206) = B_206
      | ~ v4_pre_topc(B_206,A_205)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_691,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_688])).

tff(c_698,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_691])).

tff(c_489,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_660,plain,(
    ! [B_200,A_201] :
      ( v2_tops_1(B_200,A_201)
      | ~ v3_tops_1(B_200,A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_663,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_660])).

tff(c_670,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_489,c_663])).

tff(c_704,plain,(
    ! [A_207,B_208] :
      ( k1_tops_1(A_207,B_208) = k1_xboole_0
      | ~ v2_tops_1(B_208,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_707,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_704])).

tff(c_714,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_670,c_707])).

tff(c_834,plain,(
    ! [A_240,B_241] :
      ( k7_subset_1(u1_struct_0(A_240),k2_pre_topc(A_240,B_241),k1_tops_1(A_240,B_241)) = k2_tops_1(A_240,B_241)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_846,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_834])).

tff(c_855,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_641,c_579,c_698,c_846])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.55  
% 3.45/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.55  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.45/1.55  
% 3.45/1.55  %Foreground sorts:
% 3.45/1.55  
% 3.45/1.55  
% 3.45/1.55  %Background operators:
% 3.45/1.55  
% 3.45/1.55  
% 3.45/1.55  %Foreground operators:
% 3.45/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.45/1.55  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.45/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.55  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.45/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.45/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.45/1.55  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.45/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.45/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.45/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.45/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.55  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.45/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.55  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.45/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.55  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.45/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.45/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.45/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.45/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.45/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.45/1.55  
% 3.45/1.57  tff(f_147, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.45/1.57  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.45/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.45/1.57  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.45/1.57  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 3.45/1.57  tff(f_67, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.45/1.57  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.45/1.57  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.45/1.57  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.45/1.57  tff(f_59, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.45/1.57  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.45/1.57  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.45/1.57  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.45/1.57  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.45/1.57  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.45/1.57  tff(c_66, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.45/1.57  tff(c_107, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 3.45/1.57  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.45/1.57  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.45/1.57  tff(c_308, plain, (![A_118, B_119]: (k1_tops_1(A_118, B_119)=k1_xboole_0 | ~v2_tops_1(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.45/1.57  tff(c_311, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_308])).
% 3.45/1.57  tff(c_318, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_311])).
% 3.45/1.57  tff(c_320, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_318])).
% 3.45/1.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.57  tff(c_72, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.45/1.57  tff(c_117, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_107, c_72])).
% 3.45/1.57  tff(c_378, plain, (![B_136, A_137]: (v2_tops_1(B_136, A_137) | ~r1_tarski(B_136, k2_tops_1(A_137, B_136)) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.45/1.57  tff(c_380, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_378])).
% 3.45/1.57  tff(c_385, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6, c_380])).
% 3.45/1.57  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_385])).
% 3.45/1.57  tff(c_389, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_318])).
% 3.45/1.57  tff(c_60, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.45/1.57  tff(c_475, plain, (![B_158, A_159]: (v3_tops_1(B_158, A_159) | ~v4_pre_topc(B_158, A_159) | ~v2_tops_1(B_158, A_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.45/1.57  tff(c_478, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_475])).
% 3.45/1.57  tff(c_485, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_389, c_60, c_478])).
% 3.45/1.57  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_485])).
% 3.45/1.57  tff(c_488, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 3.45/1.57  tff(c_36, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.45/1.57  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.57  tff(c_608, plain, (![A_190, B_191]: (k1_subset_1(A_190)=B_191 | ~r1_tarski(B_191, k3_subset_1(A_190, B_191)) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.45/1.57  tff(c_615, plain, (![A_190]: (k1_subset_1(A_190)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_190)))), inference(resolution, [status(thm)], [c_10, c_608])).
% 3.45/1.57  tff(c_619, plain, (![A_190]: (k1_subset_1(A_190)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_615])).
% 3.45/1.57  tff(c_24, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.45/1.57  tff(c_30, plain, (![A_39]: (k3_subset_1(A_39, k1_subset_1(A_39))=k2_subset_1(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.45/1.57  tff(c_74, plain, (![A_39]: (k3_subset_1(A_39, k1_subset_1(A_39))=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 3.45/1.57  tff(c_631, plain, (![A_39]: (k3_subset_1(A_39, k1_xboole_0)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_619, c_74])).
% 3.45/1.57  tff(c_543, plain, (![A_171, B_172]: (k4_xboole_0(A_171, B_172)=k3_subset_1(A_171, B_172) | ~m1_subset_1(B_172, k1_zfmisc_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.57  tff(c_551, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_subset_1(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_543])).
% 3.45/1.57  tff(c_641, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_631, c_551])).
% 3.45/1.57  tff(c_574, plain, (![A_180, B_181, C_182]: (k7_subset_1(A_180, B_181, C_182)=k4_xboole_0(B_181, C_182) | ~m1_subset_1(B_181, k1_zfmisc_1(A_180)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.45/1.57  tff(c_579, plain, (![C_182]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_182)=k4_xboole_0('#skF_2', C_182))), inference(resolution, [status(thm)], [c_62, c_574])).
% 3.45/1.57  tff(c_688, plain, (![A_205, B_206]: (k2_pre_topc(A_205, B_206)=B_206 | ~v4_pre_topc(B_206, A_205) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.45/1.57  tff(c_691, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_688])).
% 3.45/1.57  tff(c_698, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_691])).
% 3.45/1.57  tff(c_489, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 3.45/1.57  tff(c_660, plain, (![B_200, A_201]: (v2_tops_1(B_200, A_201) | ~v3_tops_1(B_200, A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.57  tff(c_663, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_660])).
% 3.45/1.57  tff(c_670, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_489, c_663])).
% 3.45/1.57  tff(c_704, plain, (![A_207, B_208]: (k1_tops_1(A_207, B_208)=k1_xboole_0 | ~v2_tops_1(B_208, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.45/1.57  tff(c_707, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_704])).
% 3.45/1.57  tff(c_714, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_670, c_707])).
% 3.45/1.57  tff(c_834, plain, (![A_240, B_241]: (k7_subset_1(u1_struct_0(A_240), k2_pre_topc(A_240, B_241), k1_tops_1(A_240, B_241))=k2_tops_1(A_240, B_241) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.45/1.57  tff(c_846, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_714, c_834])).
% 3.45/1.57  tff(c_855, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_641, c_579, c_698, c_846])).
% 3.45/1.57  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_855])).
% 3.45/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.57  
% 3.45/1.57  Inference rules
% 3.45/1.57  ----------------------
% 3.45/1.57  #Ref     : 0
% 3.45/1.57  #Sup     : 159
% 3.45/1.57  #Fact    : 0
% 3.45/1.57  #Define  : 0
% 3.45/1.57  #Split   : 2
% 3.45/1.57  #Chain   : 0
% 3.45/1.57  #Close   : 0
% 3.45/1.57  
% 3.45/1.57  Ordering : KBO
% 3.45/1.57  
% 3.45/1.57  Simplification rules
% 3.45/1.57  ----------------------
% 3.45/1.57  #Subsume      : 8
% 3.45/1.57  #Demod        : 89
% 3.45/1.57  #Tautology    : 112
% 3.45/1.57  #SimpNegUnit  : 7
% 3.45/1.57  #BackRed      : 8
% 3.45/1.57  
% 3.45/1.57  #Partial instantiations: 0
% 3.45/1.57  #Strategies tried      : 1
% 3.45/1.57  
% 3.45/1.57  Timing (in seconds)
% 3.45/1.57  ----------------------
% 3.45/1.57  Preprocessing        : 0.39
% 3.45/1.57  Parsing              : 0.21
% 3.45/1.57  CNF conversion       : 0.03
% 3.45/1.57  Main loop            : 0.35
% 3.45/1.57  Inferencing          : 0.14
% 3.45/1.57  Reduction            : 0.11
% 3.45/1.57  Demodulation         : 0.08
% 3.45/1.57  BG Simplification    : 0.02
% 3.45/1.57  Subsumption          : 0.05
% 3.45/1.57  Abstraction          : 0.02
% 3.45/1.57  MUC search           : 0.00
% 3.45/1.57  Cooper               : 0.00
% 3.45/1.57  Total                : 0.78
% 3.45/1.57  Index Insertion      : 0.00
% 3.45/1.57  Index Deletion       : 0.00
% 3.45/1.58  Index Matching       : 0.00
% 3.45/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
