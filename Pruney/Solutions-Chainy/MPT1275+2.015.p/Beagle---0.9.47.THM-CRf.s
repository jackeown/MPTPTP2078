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
% DateTime   : Thu Dec  3 10:22:03 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 155 expanded)
%              Number of leaves         :   48 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 321 expanded)
%              Number of equality atoms :   41 (  79 expanded)
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

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_109,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_47,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_70,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_101,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_102,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_255,plain,(
    ! [A_111,B_112] :
      ( k1_tops_1(A_111,B_112) = k1_xboole_0
      | ~ v2_tops_1(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_258,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_255])).

tff(c_265,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_258])).

tff(c_267,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_323,plain,(
    ! [B_130,A_131] :
      ( v2_tops_1(B_130,A_131)
      | ~ r1_tarski(B_130,k2_tops_1(A_131,B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_327,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_323])).

tff(c_332,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_6,c_327])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_332])).

tff(c_336,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_58,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_237,plain,(
    ! [A_107,B_108] :
      ( k2_pre_topc(A_107,B_108) = B_108
      | ~ v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_240,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_237])).

tff(c_247,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_240])).

tff(c_384,plain,(
    ! [B_147,A_148] :
      ( v3_tops_1(B_147,A_148)
      | ~ v2_tops_1(k2_pre_topc(A_148,B_147),A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_388,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_384])).

tff(c_393,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_336,c_388])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_393])).

tff(c_396,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_396])).

tff(c_405,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_22,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_39] : k3_subset_1(A_39,k1_subset_1(A_39)) = k2_subset_1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [A_39] : k3_subset_1(A_39,k1_subset_1(A_39)) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_72,plain,(
    ! [A_39] : k3_subset_1(A_39,k1_xboole_0) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_32,plain,(
    ! [A_40] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_451,plain,(
    ! [A_160,B_161] :
      ( k4_xboole_0(A_160,B_161) = k3_subset_1(A_160,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_457,plain,(
    ! [A_40] : k4_xboole_0(A_40,k1_xboole_0) = k3_subset_1(A_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_451])).

tff(c_460,plain,(
    ! [A_40] : k4_xboole_0(A_40,k1_xboole_0) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_457])).

tff(c_492,plain,(
    ! [A_173,B_174,C_175] :
      ( k7_subset_1(A_173,B_174,C_175) = k4_xboole_0(B_174,C_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_497,plain,(
    ! [C_175] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_175) = k4_xboole_0('#skF_2',C_175) ),
    inference(resolution,[status(thm)],[c_60,c_492])).

tff(c_552,plain,(
    ! [A_190,B_191] :
      ( k2_pre_topc(A_190,B_191) = B_191
      | ~ v4_pre_topc(B_191,A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_555,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_552])).

tff(c_562,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_555])).

tff(c_404,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_526,plain,(
    ! [B_184,A_185] :
      ( v2_tops_1(B_184,A_185)
      | ~ v3_tops_1(B_184,A_185)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_529,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_526])).

tff(c_536,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_404,c_529])).

tff(c_564,plain,(
    ! [A_192,B_193] :
      ( k1_tops_1(A_192,B_193) = k1_xboole_0
      | ~ v2_tops_1(B_193,A_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_567,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_564])).

tff(c_574,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_536,c_567])).

tff(c_677,plain,(
    ! [A_223,B_224] :
      ( k7_subset_1(u1_struct_0(A_223),k2_pre_topc(A_223,B_224),k1_tops_1(A_223,B_224)) = k2_tops_1(A_223,B_224)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_686,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_677])).

tff(c_693,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_460,c_497,c_562,c_686])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.65  
% 3.24/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.66  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.24/1.66  
% 3.24/1.66  %Foreground sorts:
% 3.24/1.66  
% 3.24/1.66  
% 3.24/1.66  %Background operators:
% 3.24/1.66  
% 3.24/1.66  
% 3.24/1.66  %Foreground operators:
% 3.24/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.24/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.66  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.24/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.66  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.24/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.24/1.66  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.24/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.24/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.24/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.66  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.24/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.24/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.24/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.24/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.24/1.66  
% 3.24/1.67  tff(f_139, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.24/1.67  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.24/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.67  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.24/1.67  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.24/1.67  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 3.24/1.67  tff(f_47, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.24/1.67  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.24/1.67  tff(f_59, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.24/1.67  tff(f_61, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.24/1.67  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.24/1.67  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.24/1.67  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.24/1.67  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.24/1.67  tff(c_70, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.67  tff(c_101, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_70])).
% 3.24/1.67  tff(c_64, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.67  tff(c_102, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 3.24/1.67  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.67  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.67  tff(c_255, plain, (![A_111, B_112]: (k1_tops_1(A_111, B_112)=k1_xboole_0 | ~v2_tops_1(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.24/1.67  tff(c_258, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_255])).
% 3.24/1.67  tff(c_265, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_258])).
% 3.24/1.67  tff(c_267, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_265])).
% 3.24/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.67  tff(c_323, plain, (![B_130, A_131]: (v2_tops_1(B_130, A_131) | ~r1_tarski(B_130, k2_tops_1(A_131, B_130)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.24/1.67  tff(c_327, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_323])).
% 3.24/1.67  tff(c_332, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_6, c_327])).
% 3.24/1.67  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_332])).
% 3.24/1.67  tff(c_336, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_265])).
% 3.24/1.67  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.67  tff(c_237, plain, (![A_107, B_108]: (k2_pre_topc(A_107, B_108)=B_108 | ~v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.24/1.67  tff(c_240, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_237])).
% 3.24/1.67  tff(c_247, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_240])).
% 3.24/1.67  tff(c_384, plain, (![B_147, A_148]: (v3_tops_1(B_147, A_148) | ~v2_tops_1(k2_pre_topc(A_148, B_147), A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.24/1.67  tff(c_388, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_247, c_384])).
% 3.24/1.67  tff(c_393, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_336, c_388])).
% 3.24/1.67  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_393])).
% 3.24/1.67  tff(c_396, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 3.24/1.67  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_396])).
% 3.24/1.67  tff(c_405, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 3.24/1.67  tff(c_22, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.67  tff(c_24, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.67  tff(c_30, plain, (![A_39]: (k3_subset_1(A_39, k1_subset_1(A_39))=k2_subset_1(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.24/1.67  tff(c_71, plain, (![A_39]: (k3_subset_1(A_39, k1_subset_1(A_39))=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 3.24/1.67  tff(c_72, plain, (![A_39]: (k3_subset_1(A_39, k1_xboole_0)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_71])).
% 3.24/1.67  tff(c_32, plain, (![A_40]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.67  tff(c_451, plain, (![A_160, B_161]: (k4_xboole_0(A_160, B_161)=k3_subset_1(A_160, B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.67  tff(c_457, plain, (![A_40]: (k4_xboole_0(A_40, k1_xboole_0)=k3_subset_1(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_451])).
% 3.24/1.67  tff(c_460, plain, (![A_40]: (k4_xboole_0(A_40, k1_xboole_0)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_457])).
% 3.24/1.67  tff(c_492, plain, (![A_173, B_174, C_175]: (k7_subset_1(A_173, B_174, C_175)=k4_xboole_0(B_174, C_175) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.67  tff(c_497, plain, (![C_175]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_175)=k4_xboole_0('#skF_2', C_175))), inference(resolution, [status(thm)], [c_60, c_492])).
% 3.24/1.67  tff(c_552, plain, (![A_190, B_191]: (k2_pre_topc(A_190, B_191)=B_191 | ~v4_pre_topc(B_191, A_190) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.24/1.67  tff(c_555, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_552])).
% 3.24/1.67  tff(c_562, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_555])).
% 3.24/1.67  tff(c_404, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 3.24/1.67  tff(c_526, plain, (![B_184, A_185]: (v2_tops_1(B_184, A_185) | ~v3_tops_1(B_184, A_185) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.24/1.67  tff(c_529, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_526])).
% 3.24/1.67  tff(c_536, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_404, c_529])).
% 3.24/1.67  tff(c_564, plain, (![A_192, B_193]: (k1_tops_1(A_192, B_193)=k1_xboole_0 | ~v2_tops_1(B_193, A_192) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.24/1.67  tff(c_567, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_564])).
% 3.24/1.67  tff(c_574, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_536, c_567])).
% 3.24/1.67  tff(c_677, plain, (![A_223, B_224]: (k7_subset_1(u1_struct_0(A_223), k2_pre_topc(A_223, B_224), k1_tops_1(A_223, B_224))=k2_tops_1(A_223, B_224) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.24/1.67  tff(c_686, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_574, c_677])).
% 3.24/1.67  tff(c_693, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_460, c_497, c_562, c_686])).
% 3.24/1.67  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_405, c_693])).
% 3.24/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.67  
% 3.24/1.67  Inference rules
% 3.24/1.67  ----------------------
% 3.24/1.67  #Ref     : 0
% 3.24/1.67  #Sup     : 130
% 3.24/1.67  #Fact    : 0
% 3.24/1.67  #Define  : 0
% 3.24/1.67  #Split   : 3
% 3.24/1.67  #Chain   : 0
% 3.24/1.67  #Close   : 0
% 3.24/1.67  
% 3.24/1.67  Ordering : KBO
% 3.24/1.67  
% 3.24/1.67  Simplification rules
% 3.24/1.67  ----------------------
% 3.24/1.67  #Subsume      : 5
% 3.24/1.67  #Demod        : 68
% 3.24/1.67  #Tautology    : 88
% 3.24/1.67  #SimpNegUnit  : 6
% 3.24/1.67  #BackRed      : 0
% 3.24/1.67  
% 3.24/1.67  #Partial instantiations: 0
% 3.24/1.67  #Strategies tried      : 1
% 3.24/1.67  
% 3.24/1.67  Timing (in seconds)
% 3.24/1.67  ----------------------
% 3.24/1.67  Preprocessing        : 0.47
% 3.24/1.67  Parsing              : 0.22
% 3.24/1.68  CNF conversion       : 0.04
% 3.24/1.68  Main loop            : 0.34
% 3.24/1.68  Inferencing          : 0.14
% 3.24/1.68  Reduction            : 0.10
% 3.24/1.68  Demodulation         : 0.07
% 3.24/1.68  BG Simplification    : 0.02
% 3.24/1.68  Subsumption          : 0.05
% 3.24/1.68  Abstraction          : 0.02
% 3.24/1.68  MUC search           : 0.00
% 3.24/1.68  Cooper               : 0.00
% 3.24/1.68  Total                : 0.85
% 3.24/1.68  Index Insertion      : 0.00
% 3.24/1.68  Index Deletion       : 0.00
% 3.24/1.68  Index Matching       : 0.00
% 3.24/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
