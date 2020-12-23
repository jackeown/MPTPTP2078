%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:07 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 169 expanded)
%              Number of leaves         :   50 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 345 expanded)
%              Number of equality atoms :   44 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_96,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_68,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_94,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1265,plain,(
    ! [B_179,A_180] :
      ( v2_tops_1(B_179,A_180)
      | k1_tops_1(A_180,B_179) != k1_xboole_0
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1279,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_1265])).

tff(c_1295,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1279])).

tff(c_1298,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_1358,plain,(
    ! [A_187,B_188] :
      ( k1_tops_1(A_187,B_188) = k1_xboole_0
      | ~ v2_tops_1(B_188,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1372,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_1358])).

tff(c_1389,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1372])).

tff(c_1390,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1298,c_1389])).

tff(c_18,plain,(
    ! [A_31] : k2_subset_1(A_31) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_34] : m1_subset_1(k2_subset_1(A_34),k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_34] : m1_subset_1(A_34,k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_95,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_110,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_77,c_95])).

tff(c_74,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_114,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_74])).

tff(c_1686,plain,(
    ! [B_210,A_211] :
      ( v2_tops_1(B_210,A_211)
      | ~ r1_tarski(B_210,k2_tops_1(A_211,B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1692,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1686])).

tff(c_1701,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_110,c_1692])).

tff(c_1703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1390,c_1701])).

tff(c_1704,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_62,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2278,plain,(
    ! [B_257,A_258] :
      ( v3_tops_1(B_257,A_258)
      | ~ v4_pre_topc(B_257,A_258)
      | ~ v2_tops_1(B_257,A_258)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2292,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2278])).

tff(c_2309,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1704,c_62,c_2292])).

tff(c_2311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2309])).

tff(c_2312,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_34,plain,(
    ! [A_44] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2371,plain,(
    ! [A_271,B_272] :
      ( k3_subset_1(A_271,k3_subset_1(A_271,B_272)) = B_272
      | ~ m1_subset_1(B_272,k1_zfmisc_1(A_271)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2383,plain,(
    ! [A_44] : k3_subset_1(A_44,k3_subset_1(A_44,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_2371])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( k2_subset_1(A_42) = B_43
      | ~ r1_tarski(k3_subset_1(A_42,B_43),B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2638,plain,(
    ! [B_303,A_304] :
      ( B_303 = A_304
      | ~ r1_tarski(k3_subset_1(A_304,B_303),B_303)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(A_304)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_2651,plain,(
    ! [A_44] :
      ( k3_subset_1(A_44,k1_xboole_0) = A_44
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_44,k1_xboole_0))
      | ~ m1_subset_1(k3_subset_1(A_44,k1_xboole_0),k1_zfmisc_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2383,c_2638])).

tff(c_2668,plain,(
    ! [A_305] :
      ( k3_subset_1(A_305,k1_xboole_0) = A_305
      | ~ m1_subset_1(k3_subset_1(A_305,k1_xboole_0),k1_zfmisc_1(A_305)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2651])).

tff(c_2672,plain,(
    ! [A_35] :
      ( k3_subset_1(A_35,k1_xboole_0) = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2668])).

tff(c_2679,plain,(
    ! [A_35] : k3_subset_1(A_35,k1_xboole_0) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2672])).

tff(c_2506,plain,(
    ! [A_279,B_280] :
      ( k4_xboole_0(A_279,B_280) = k3_subset_1(A_279,B_280)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(A_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2526,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = k3_subset_1(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_2506])).

tff(c_2682,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_2526])).

tff(c_2313,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2881,plain,(
    ! [B_319,A_320] :
      ( v2_tops_1(B_319,A_320)
      | ~ v3_tops_1(B_319,A_320)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2892,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2881])).

tff(c_2905,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2313,c_2892])).

tff(c_3224,plain,(
    ! [A_347,B_348] :
      ( k1_tops_1(A_347,B_348) = k1_xboole_0
      | ~ v2_tops_1(B_348,A_347)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3238,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_3224])).

tff(c_3254,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2905,c_3238])).

tff(c_2727,plain,(
    ! [A_307,B_308,C_309] :
      ( k7_subset_1(A_307,B_308,C_309) = k4_xboole_0(B_308,C_309)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2740,plain,(
    ! [C_309] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_309) = k4_xboole_0('#skF_2',C_309) ),
    inference(resolution,[status(thm)],[c_64,c_2727])).

tff(c_3392,plain,(
    ! [A_354,B_355] :
      ( k2_pre_topc(A_354,B_355) = B_355
      | ~ v4_pre_topc(B_355,A_354)
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3406,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_3392])).

tff(c_3422,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_3406])).

tff(c_4095,plain,(
    ! [A_413,B_414] :
      ( k7_subset_1(u1_struct_0(A_413),k2_pre_topc(A_413,B_414),k1_tops_1(A_413,B_414)) = k2_tops_1(A_413,B_414)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4107,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3422,c_4095])).

tff(c_4116,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2682,c_3254,c_2740,c_4107])).

tff(c_4118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2312,c_4116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.87  
% 4.80/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.88  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.80/1.88  
% 4.80/1.88  %Foreground sorts:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Background operators:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Foreground operators:
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.80/1.88  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.80/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.88  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.80/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.80/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.80/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.80/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.80/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.80/1.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.80/1.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.80/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.88  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.80/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.80/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.80/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.80/1.88  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.80/1.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.80/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.80/1.88  
% 4.80/1.89  tff(f_153, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 4.80/1.89  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.80/1.89  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.80/1.89  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.80/1.89  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.80/1.89  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 4.80/1.89  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 4.80/1.89  tff(f_69, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.80/1.89  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.80/1.89  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.80/1.89  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.80/1.89  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 4.80/1.89  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.80/1.89  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 4.80/1.89  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.80/1.89  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.80/1.89  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.80/1.89  tff(c_68, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.80/1.89  tff(c_94, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 4.80/1.89  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.80/1.89  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.80/1.89  tff(c_1265, plain, (![B_179, A_180]: (v2_tops_1(B_179, A_180) | k1_tops_1(A_180, B_179)!=k1_xboole_0 | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.80/1.89  tff(c_1279, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_1265])).
% 4.80/1.89  tff(c_1295, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1279])).
% 4.80/1.89  tff(c_1298, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1295])).
% 4.80/1.89  tff(c_1358, plain, (![A_187, B_188]: (k1_tops_1(A_187, B_188)=k1_xboole_0 | ~v2_tops_1(B_188, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.80/1.89  tff(c_1372, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_1358])).
% 4.80/1.89  tff(c_1389, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1372])).
% 4.80/1.89  tff(c_1390, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1298, c_1389])).
% 4.80/1.89  tff(c_18, plain, (![A_31]: (k2_subset_1(A_31)=A_31)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.80/1.89  tff(c_22, plain, (![A_34]: (m1_subset_1(k2_subset_1(A_34), k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.80/1.89  tff(c_77, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 4.80/1.89  tff(c_95, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/1.89  tff(c_110, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_77, c_95])).
% 4.80/1.89  tff(c_74, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.80/1.89  tff(c_114, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_74])).
% 4.80/1.89  tff(c_1686, plain, (![B_210, A_211]: (v2_tops_1(B_210, A_211) | ~r1_tarski(B_210, k2_tops_1(A_211, B_210)) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_211))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.80/1.89  tff(c_1692, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_114, c_1686])).
% 4.80/1.89  tff(c_1701, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_110, c_1692])).
% 4.80/1.89  tff(c_1703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1390, c_1701])).
% 4.80/1.89  tff(c_1704, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_1295])).
% 4.80/1.89  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.80/1.89  tff(c_2278, plain, (![B_257, A_258]: (v3_tops_1(B_257, A_258) | ~v4_pre_topc(B_257, A_258) | ~v2_tops_1(B_257, A_258) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.80/1.89  tff(c_2292, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_2278])).
% 4.80/1.89  tff(c_2309, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1704, c_62, c_2292])).
% 4.80/1.89  tff(c_2311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_2309])).
% 4.80/1.89  tff(c_2312, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 4.80/1.89  tff(c_34, plain, (![A_44]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/1.89  tff(c_24, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.80/1.89  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.80/1.89  tff(c_2371, plain, (![A_271, B_272]: (k3_subset_1(A_271, k3_subset_1(A_271, B_272))=B_272 | ~m1_subset_1(B_272, k1_zfmisc_1(A_271)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.80/1.89  tff(c_2383, plain, (![A_44]: (k3_subset_1(A_44, k3_subset_1(A_44, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2371])).
% 4.80/1.89  tff(c_32, plain, (![A_42, B_43]: (k2_subset_1(A_42)=B_43 | ~r1_tarski(k3_subset_1(A_42, B_43), B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.80/1.89  tff(c_2638, plain, (![B_303, A_304]: (B_303=A_304 | ~r1_tarski(k3_subset_1(A_304, B_303), B_303) | ~m1_subset_1(B_303, k1_zfmisc_1(A_304)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 4.80/1.89  tff(c_2651, plain, (![A_44]: (k3_subset_1(A_44, k1_xboole_0)=A_44 | ~r1_tarski(k1_xboole_0, k3_subset_1(A_44, k1_xboole_0)) | ~m1_subset_1(k3_subset_1(A_44, k1_xboole_0), k1_zfmisc_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_2383, c_2638])).
% 4.80/1.89  tff(c_2668, plain, (![A_305]: (k3_subset_1(A_305, k1_xboole_0)=A_305 | ~m1_subset_1(k3_subset_1(A_305, k1_xboole_0), k1_zfmisc_1(A_305)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2651])).
% 4.80/1.89  tff(c_2672, plain, (![A_35]: (k3_subset_1(A_35, k1_xboole_0)=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(resolution, [status(thm)], [c_24, c_2668])).
% 4.80/1.89  tff(c_2679, plain, (![A_35]: (k3_subset_1(A_35, k1_xboole_0)=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2672])).
% 4.80/1.89  tff(c_2506, plain, (![A_279, B_280]: (k4_xboole_0(A_279, B_280)=k3_subset_1(A_279, B_280) | ~m1_subset_1(B_280, k1_zfmisc_1(A_279)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.89  tff(c_2526, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=k3_subset_1(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_2506])).
% 4.80/1.89  tff(c_2682, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_2526])).
% 4.80/1.89  tff(c_2313, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 4.80/1.89  tff(c_2881, plain, (![B_319, A_320]: (v2_tops_1(B_319, A_320) | ~v3_tops_1(B_319, A_320) | ~m1_subset_1(B_319, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.80/1.89  tff(c_2892, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_2881])).
% 4.80/1.89  tff(c_2905, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2313, c_2892])).
% 4.80/1.89  tff(c_3224, plain, (![A_347, B_348]: (k1_tops_1(A_347, B_348)=k1_xboole_0 | ~v2_tops_1(B_348, A_347) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.80/1.89  tff(c_3238, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_3224])).
% 4.80/1.89  tff(c_3254, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2905, c_3238])).
% 4.80/1.89  tff(c_2727, plain, (![A_307, B_308, C_309]: (k7_subset_1(A_307, B_308, C_309)=k4_xboole_0(B_308, C_309) | ~m1_subset_1(B_308, k1_zfmisc_1(A_307)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.80/1.89  tff(c_2740, plain, (![C_309]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_309)=k4_xboole_0('#skF_2', C_309))), inference(resolution, [status(thm)], [c_64, c_2727])).
% 4.80/1.89  tff(c_3392, plain, (![A_354, B_355]: (k2_pre_topc(A_354, B_355)=B_355 | ~v4_pre_topc(B_355, A_354) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.80/1.89  tff(c_3406, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_3392])).
% 4.80/1.89  tff(c_3422, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_3406])).
% 4.80/1.89  tff(c_4095, plain, (![A_413, B_414]: (k7_subset_1(u1_struct_0(A_413), k2_pre_topc(A_413, B_414), k1_tops_1(A_413, B_414))=k2_tops_1(A_413, B_414) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.80/1.89  tff(c_4107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3422, c_4095])).
% 4.80/1.89  tff(c_4116, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2682, c_3254, c_2740, c_4107])).
% 4.80/1.89  tff(c_4118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2312, c_4116])).
% 4.80/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.89  
% 4.80/1.89  Inference rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Ref     : 0
% 4.80/1.89  #Sup     : 861
% 4.80/1.89  #Fact    : 0
% 4.80/1.89  #Define  : 0
% 4.80/1.89  #Split   : 16
% 4.80/1.89  #Chain   : 0
% 4.80/1.89  #Close   : 0
% 4.80/1.89  
% 4.80/1.89  Ordering : KBO
% 4.80/1.89  
% 4.80/1.89  Simplification rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Subsume      : 155
% 4.80/1.89  #Demod        : 602
% 4.80/1.89  #Tautology    : 487
% 4.80/1.89  #SimpNegUnit  : 21
% 4.80/1.89  #BackRed      : 18
% 4.80/1.89  
% 4.80/1.89  #Partial instantiations: 0
% 4.80/1.89  #Strategies tried      : 1
% 4.80/1.89  
% 4.80/1.89  Timing (in seconds)
% 4.80/1.89  ----------------------
% 4.80/1.90  Preprocessing        : 0.36
% 4.80/1.90  Parsing              : 0.19
% 4.80/1.90  CNF conversion       : 0.02
% 4.80/1.90  Main loop            : 0.78
% 4.80/1.90  Inferencing          : 0.28
% 4.80/1.90  Reduction            : 0.27
% 4.80/1.90  Demodulation         : 0.20
% 4.80/1.90  BG Simplification    : 0.04
% 4.80/1.90  Subsumption          : 0.14
% 4.80/1.90  Abstraction          : 0.04
% 4.80/1.90  MUC search           : 0.00
% 4.80/1.90  Cooper               : 0.00
% 4.80/1.90  Total                : 1.17
% 4.80/1.90  Index Insertion      : 0.00
% 4.80/1.90  Index Deletion       : 0.00
% 4.80/1.90  Index Matching       : 0.00
% 4.80/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
