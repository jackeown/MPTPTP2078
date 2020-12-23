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
% DateTime   : Thu Dec  3 10:22:03 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 653 expanded)
%              Number of leaves         :   56 ( 246 expanded)
%              Depth                    :   16
%              Number of atoms          :  246 (1724 expanded)
%              Number of equality atoms :   56 ( 376 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_182,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_112,axiom,(
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

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_162,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_83,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_171,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_88,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_101,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,
    ( k2_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_116,plain,(
    ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_82])).

tff(c_80,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_650,plain,(
    ! [A_183,B_184] :
      ( k1_tops_1(A_183,B_184) = k1_xboole_0
      | ~ v2_tops_1(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_673,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_650])).

tff(c_685,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_673])).

tff(c_765,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1230,plain,(
    ! [B_215,A_216] :
      ( v2_tops_1(B_215,A_216)
      | ~ r1_tarski(B_215,k2_tops_1(A_216,B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1235,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1230])).

tff(c_1240,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_12,c_1235])).

tff(c_1242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_1240])).

tff(c_1244,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_76,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1938,plain,(
    ! [B_258,A_259] :
      ( v3_tops_1(B_258,A_259)
      | ~ v4_pre_topc(B_258,A_259)
      | ~ v2_tops_1(B_258,A_259)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1964,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1938])).

tff(c_1977,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1244,c_76,c_1964])).

tff(c_1979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_1977])).

tff(c_1981,plain,(
    k2_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_34,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k3_subset_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2593,plain,(
    ! [A_351,B_352] :
      ( k2_pre_topc(A_351,B_352) = B_352
      | ~ v4_pre_topc(B_352,A_351)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2616,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2593])).

tff(c_2628,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2616])).

tff(c_2955,plain,(
    ! [A_374,B_375] :
      ( k2_pre_topc(A_374,B_375) = k2_struct_0(A_374)
      | ~ v1_tops_1(B_375,A_374)
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ l1_pre_topc(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2981,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2955])).

tff(c_2994,plain,
    ( k2_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2628,c_2981])).

tff(c_3034,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2994])).

tff(c_2141,plain,(
    ! [A_301,B_302] :
      ( k3_subset_1(A_301,k3_subset_1(A_301,B_302)) = B_302
      | ~ m1_subset_1(B_302,k1_zfmisc_1(A_301)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2156,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_2141])).

tff(c_3576,plain,(
    ! [A_414,B_415] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_414),B_415),A_414)
      | ~ v3_tops_1(B_415,A_414)
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3579,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_3576])).

tff(c_3589,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3579])).

tff(c_3590,plain,
    ( ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3034,c_3589])).

tff(c_3783,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3590])).

tff(c_3786,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_34,c_3783])).

tff(c_3790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3786])).

tff(c_3792,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3590])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    ! [A_53] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_53)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2065,plain,(
    ! [A_282,B_283] :
      ( k4_xboole_0(A_282,B_283) = k3_subset_1(A_282,B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(A_282)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2071,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = k3_subset_1(A_53,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_2065])).

tff(c_2074,plain,(
    ! [A_53] : k3_subset_1(A_53,k1_xboole_0) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2071])).

tff(c_1980,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2462,plain,(
    ! [B_345,A_346] :
      ( v2_tops_1(B_345,A_346)
      | ~ v3_tops_1(B_345,A_346)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2489,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ v3_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2462])).

tff(c_2502,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1980,c_2489])).

tff(c_2635,plain,(
    ! [A_354,B_355] :
      ( k1_tops_1(A_354,B_355) = k1_xboole_0
      | ~ v2_tops_1(B_355,A_354)
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2658,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2635])).

tff(c_2670,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2502,c_2658])).

tff(c_70,plain,(
    ! [A_79,B_81] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_79),B_81),A_79)
      | ~ v3_tops_1(B_81,A_79)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    ! [A_70,B_72] :
      ( k2_pre_topc(A_70,B_72) = k2_struct_0(A_70)
      | ~ v1_tops_1(B_72,A_70)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3806,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3792,c_60])).

tff(c_3846,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3806])).

tff(c_6677,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3846])).

tff(c_6680,plain,
    ( ~ v3_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6677])).

tff(c_6684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1980,c_6680])).

tff(c_6685,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3846])).

tff(c_54,plain,(
    ! [A_64,B_66] :
      ( k3_subset_1(u1_struct_0(A_64),k2_pre_topc(A_64,k3_subset_1(u1_struct_0(A_64),B_66))) = k1_tops_1(A_64,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6710,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) = k1_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6685,c_54])).

tff(c_6731,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2670,c_6710])).

tff(c_2782,plain,(
    ! [A_365,B_366] :
      ( m1_subset_1(k2_pre_topc(A_365,B_366),k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7017,plain,(
    ! [A_588,B_589] :
      ( k3_subset_1(u1_struct_0(A_588),k3_subset_1(u1_struct_0(A_588),k2_pre_topc(A_588,B_589))) = k2_pre_topc(A_588,B_589)
      | ~ m1_subset_1(B_589,k1_zfmisc_1(u1_struct_0(A_588)))
      | ~ l1_pre_topc(A_588) ) ),
    inference(resolution,[status(thm)],[c_2782,c_36])).

tff(c_7056,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6685,c_7017])).

tff(c_7077,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3792,c_2074,c_6731,c_6685,c_7056])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2111,plain,(
    ! [C_293,A_294,B_295] :
      ( r2_hidden(C_293,A_294)
      | ~ r2_hidden(C_293,B_295)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(A_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2395,plain,(
    ! [A_340,B_341,A_342] :
      ( r2_hidden('#skF_1'(A_340,B_341),A_342)
      | ~ m1_subset_1(A_340,k1_zfmisc_1(A_342))
      | r1_tarski(A_340,B_341) ) ),
    inference(resolution,[status(thm)],[c_6,c_2111])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2424,plain,(
    ! [A_343,A_344] :
      ( ~ m1_subset_1(A_343,k1_zfmisc_1(A_344))
      | r1_tarski(A_343,A_344) ) ),
    inference(resolution,[status(thm)],[c_2395,c_4])).

tff(c_2460,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_2424])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2520,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2460,c_16])).

tff(c_7123,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7077,c_2520])).

tff(c_2115,plain,(
    ! [A_296,B_297] :
      ( m1_subset_1(k3_subset_1(A_296,B_297),k1_zfmisc_1(A_296))
      | ~ m1_subset_1(B_297,k1_zfmisc_1(A_296)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2123,plain,(
    ! [A_53] :
      ( m1_subset_1(A_53,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_2115])).

tff(c_2127,plain,(
    ! [A_53] : m1_subset_1(A_53,k1_zfmisc_1(A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2123])).

tff(c_2230,plain,(
    ! [A_308,B_309,C_310] :
      ( k9_subset_1(A_308,B_309,C_310) = k3_xboole_0(B_309,C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(A_308)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2246,plain,(
    ! [A_53,B_309] : k9_subset_1(A_53,B_309,A_53) = k3_xboole_0(B_309,A_53) ),
    inference(resolution,[status(thm)],[c_2127,c_2230])).

tff(c_4028,plain,(
    ! [A_441,B_442] :
      ( k9_subset_1(u1_struct_0(A_441),k2_pre_topc(A_441,B_442),k2_pre_topc(A_441,k3_subset_1(u1_struct_0(A_441),B_442))) = k2_tops_1(A_441,B_442)
      | ~ m1_subset_1(B_442,k1_zfmisc_1(u1_struct_0(A_441)))
      | ~ l1_pre_topc(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4046,plain,
    ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_4028])).

tff(c_4061,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_4046])).

tff(c_6688,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6685,c_4061])).

tff(c_7942,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_2246,c_7077,c_6688])).

tff(c_7943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1981,c_7942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.73  
% 7.65/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/2.74  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.78/2.74  
% 7.78/2.74  %Foreground sorts:
% 7.78/2.74  
% 7.78/2.74  
% 7.78/2.74  %Background operators:
% 7.78/2.74  
% 7.78/2.74  
% 7.78/2.74  %Foreground operators:
% 7.78/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.78/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.78/2.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.78/2.74  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.78/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.78/2.74  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.78/2.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.78/2.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.78/2.74  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 7.78/2.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.78/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.78/2.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.78/2.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.78/2.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.78/2.74  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.78/2.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.78/2.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.78/2.74  tff('#skF_2', type, '#skF_2': $i).
% 7.78/2.74  tff('#skF_3', type, '#skF_3': $i).
% 7.78/2.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.78/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.78/2.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.78/2.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.78/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.78/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.78/2.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.78/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.78/2.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.78/2.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.78/2.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.78/2.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.78/2.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.78/2.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.78/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.78/2.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.78/2.74  
% 7.78/2.76  tff(f_194, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 7.78/2.76  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 7.78/2.76  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.78/2.76  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 7.78/2.76  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 7.78/2.76  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.78/2.76  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.78/2.76  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 7.78/2.76  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.78/2.76  tff(f_162, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 7.78/2.76  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.78/2.76  tff(f_83, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.78/2.76  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 7.78/2.76  tff(f_171, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 7.78/2.76  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 7.78/2.76  tff(f_97, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.78/2.76  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.78/2.76  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.78/2.76  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.78/2.76  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.78/2.76  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 7.78/2.76  tff(c_88, plain, (v3_tops_1('#skF_3', '#skF_2') | k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.78/2.76  tff(c_101, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_88])).
% 7.78/2.76  tff(c_82, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.78/2.76  tff(c_116, plain, (~v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_82])).
% 7.78/2.76  tff(c_80, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.78/2.76  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.78/2.76  tff(c_650, plain, (![A_183, B_184]: (k1_tops_1(A_183, B_184)=k1_xboole_0 | ~v2_tops_1(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.78/2.76  tff(c_673, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_650])).
% 7.78/2.76  tff(c_685, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_673])).
% 7.78/2.76  tff(c_765, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_685])).
% 7.78/2.76  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.78/2.76  tff(c_1230, plain, (![B_215, A_216]: (v2_tops_1(B_215, A_216) | ~r1_tarski(B_215, k2_tops_1(A_216, B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.78/2.76  tff(c_1235, plain, (v2_tops_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_1230])).
% 7.78/2.76  tff(c_1240, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_12, c_1235])).
% 7.78/2.76  tff(c_1242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_1240])).
% 7.78/2.76  tff(c_1244, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_685])).
% 7.78/2.76  tff(c_76, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.78/2.76  tff(c_1938, plain, (![B_258, A_259]: (v3_tops_1(B_258, A_259) | ~v4_pre_topc(B_258, A_259) | ~v2_tops_1(B_258, A_259) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.78/2.76  tff(c_1964, plain, (v3_tops_1('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1938])).
% 7.78/2.76  tff(c_1977, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1244, c_76, c_1964])).
% 7.78/2.76  tff(c_1979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_1977])).
% 7.78/2.76  tff(c_1981, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_88])).
% 7.78/2.76  tff(c_34, plain, (![A_42, B_43]: (m1_subset_1(k3_subset_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.78/2.76  tff(c_2593, plain, (![A_351, B_352]: (k2_pre_topc(A_351, B_352)=B_352 | ~v4_pre_topc(B_352, A_351) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.78/2.76  tff(c_2616, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2593])).
% 7.78/2.76  tff(c_2628, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2616])).
% 7.78/2.76  tff(c_2955, plain, (![A_374, B_375]: (k2_pre_topc(A_374, B_375)=k2_struct_0(A_374) | ~v1_tops_1(B_375, A_374) | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0(A_374))) | ~l1_pre_topc(A_374))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.78/2.76  tff(c_2981, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2955])).
% 7.78/2.76  tff(c_2994, plain, (k2_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2628, c_2981])).
% 7.78/2.76  tff(c_3034, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2994])).
% 7.78/2.76  tff(c_2141, plain, (![A_301, B_302]: (k3_subset_1(A_301, k3_subset_1(A_301, B_302))=B_302 | ~m1_subset_1(B_302, k1_zfmisc_1(A_301)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.78/2.76  tff(c_2156, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_78, c_2141])).
% 7.78/2.76  tff(c_3576, plain, (![A_414, B_415]: (v1_tops_1(k3_subset_1(u1_struct_0(A_414), B_415), A_414) | ~v3_tops_1(B_415, A_414) | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0(A_414))) | ~l1_pre_topc(A_414))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.78/2.76  tff(c_3579, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2156, c_3576])).
% 7.78/2.76  tff(c_3589, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3579])).
% 7.78/2.76  tff(c_3590, plain, (~v3_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_3034, c_3589])).
% 7.78/2.76  tff(c_3783, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3590])).
% 7.78/2.76  tff(c_3786, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_3783])).
% 7.78/2.76  tff(c_3790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_3786])).
% 7.78/2.76  tff(c_3792, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3590])).
% 7.78/2.76  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.78/2.76  tff(c_42, plain, (![A_53]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.78/2.76  tff(c_2065, plain, (![A_282, B_283]: (k4_xboole_0(A_282, B_283)=k3_subset_1(A_282, B_283) | ~m1_subset_1(B_283, k1_zfmisc_1(A_282)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.78/2.76  tff(c_2071, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=k3_subset_1(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_2065])).
% 7.78/2.76  tff(c_2074, plain, (![A_53]: (k3_subset_1(A_53, k1_xboole_0)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2071])).
% 7.78/2.76  tff(c_1980, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_88])).
% 7.78/2.76  tff(c_2462, plain, (![B_345, A_346]: (v2_tops_1(B_345, A_346) | ~v3_tops_1(B_345, A_346) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.78/2.76  tff(c_2489, plain, (v2_tops_1('#skF_3', '#skF_2') | ~v3_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2462])).
% 7.78/2.76  tff(c_2502, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1980, c_2489])).
% 7.78/2.76  tff(c_2635, plain, (![A_354, B_355]: (k1_tops_1(A_354, B_355)=k1_xboole_0 | ~v2_tops_1(B_355, A_354) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.78/2.76  tff(c_2658, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2635])).
% 7.78/2.76  tff(c_2670, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2502, c_2658])).
% 7.78/2.76  tff(c_70, plain, (![A_79, B_81]: (v1_tops_1(k3_subset_1(u1_struct_0(A_79), B_81), A_79) | ~v3_tops_1(B_81, A_79) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.78/2.76  tff(c_60, plain, (![A_70, B_72]: (k2_pre_topc(A_70, B_72)=k2_struct_0(A_70) | ~v1_tops_1(B_72, A_70) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.78/2.76  tff(c_3806, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3792, c_60])).
% 7.78/2.76  tff(c_3846, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3806])).
% 7.78/2.76  tff(c_6677, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3846])).
% 7.78/2.76  tff(c_6680, plain, (~v3_tops_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_6677])).
% 7.78/2.76  tff(c_6684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1980, c_6680])).
% 7.78/2.76  tff(c_6685, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3846])).
% 7.78/2.76  tff(c_54, plain, (![A_64, B_66]: (k3_subset_1(u1_struct_0(A_64), k2_pre_topc(A_64, k3_subset_1(u1_struct_0(A_64), B_66)))=k1_tops_1(A_64, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/2.76  tff(c_6710, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))=k1_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6685, c_54])).
% 7.78/2.76  tff(c_6731, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2670, c_6710])).
% 7.78/2.76  tff(c_2782, plain, (![A_365, B_366]: (m1_subset_1(k2_pre_topc(A_365, B_366), k1_zfmisc_1(u1_struct_0(A_365))) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.78/2.76  tff(c_36, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.78/2.76  tff(c_7017, plain, (![A_588, B_589]: (k3_subset_1(u1_struct_0(A_588), k3_subset_1(u1_struct_0(A_588), k2_pre_topc(A_588, B_589)))=k2_pre_topc(A_588, B_589) | ~m1_subset_1(B_589, k1_zfmisc_1(u1_struct_0(A_588))) | ~l1_pre_topc(A_588))), inference(resolution, [status(thm)], [c_2782, c_36])).
% 7.78/2.76  tff(c_7056, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6685, c_7017])).
% 7.78/2.76  tff(c_7077, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3792, c_2074, c_6731, c_6685, c_7056])).
% 7.78/2.76  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.78/2.76  tff(c_2111, plain, (![C_293, A_294, B_295]: (r2_hidden(C_293, A_294) | ~r2_hidden(C_293, B_295) | ~m1_subset_1(B_295, k1_zfmisc_1(A_294)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.78/2.76  tff(c_2395, plain, (![A_340, B_341, A_342]: (r2_hidden('#skF_1'(A_340, B_341), A_342) | ~m1_subset_1(A_340, k1_zfmisc_1(A_342)) | r1_tarski(A_340, B_341))), inference(resolution, [status(thm)], [c_6, c_2111])).
% 7.78/2.76  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.78/2.76  tff(c_2424, plain, (![A_343, A_344]: (~m1_subset_1(A_343, k1_zfmisc_1(A_344)) | r1_tarski(A_343, A_344))), inference(resolution, [status(thm)], [c_2395, c_4])).
% 7.78/2.76  tff(c_2460, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_78, c_2424])).
% 7.78/2.76  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/2.76  tff(c_2520, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_2460, c_16])).
% 7.78/2.76  tff(c_7123, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7077, c_2520])).
% 7.78/2.76  tff(c_2115, plain, (![A_296, B_297]: (m1_subset_1(k3_subset_1(A_296, B_297), k1_zfmisc_1(A_296)) | ~m1_subset_1(B_297, k1_zfmisc_1(A_296)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.78/2.76  tff(c_2123, plain, (![A_53]: (m1_subset_1(A_53, k1_zfmisc_1(A_53)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_2115])).
% 7.78/2.76  tff(c_2127, plain, (![A_53]: (m1_subset_1(A_53, k1_zfmisc_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2123])).
% 7.78/2.76  tff(c_2230, plain, (![A_308, B_309, C_310]: (k9_subset_1(A_308, B_309, C_310)=k3_xboole_0(B_309, C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(A_308)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.78/2.76  tff(c_2246, plain, (![A_53, B_309]: (k9_subset_1(A_53, B_309, A_53)=k3_xboole_0(B_309, A_53))), inference(resolution, [status(thm)], [c_2127, c_2230])).
% 7.78/2.76  tff(c_4028, plain, (![A_441, B_442]: (k9_subset_1(u1_struct_0(A_441), k2_pre_topc(A_441, B_442), k2_pre_topc(A_441, k3_subset_1(u1_struct_0(A_441), B_442)))=k2_tops_1(A_441, B_442) | ~m1_subset_1(B_442, k1_zfmisc_1(u1_struct_0(A_441))) | ~l1_pre_topc(A_441))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.78/2.76  tff(c_4046, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_4028])).
% 7.78/2.76  tff(c_4061, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_4046])).
% 7.78/2.76  tff(c_6688, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6685, c_4061])).
% 7.78/2.76  tff(c_7942, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_2246, c_7077, c_6688])).
% 7.78/2.76  tff(c_7943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1981, c_7942])).
% 7.78/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/2.76  
% 7.78/2.76  Inference rules
% 7.78/2.76  ----------------------
% 7.78/2.76  #Ref     : 0
% 7.78/2.76  #Sup     : 1763
% 7.78/2.76  #Fact    : 0
% 7.78/2.76  #Define  : 0
% 7.78/2.76  #Split   : 27
% 7.78/2.76  #Chain   : 0
% 7.78/2.76  #Close   : 0
% 7.78/2.76  
% 7.78/2.76  Ordering : KBO
% 7.78/2.76  
% 7.78/2.76  Simplification rules
% 7.78/2.76  ----------------------
% 7.78/2.76  #Subsume      : 284
% 7.78/2.76  #Demod        : 1084
% 7.78/2.76  #Tautology    : 606
% 7.78/2.76  #SimpNegUnit  : 31
% 7.78/2.76  #BackRed      : 62
% 7.78/2.76  
% 7.78/2.76  #Partial instantiations: 0
% 7.78/2.76  #Strategies tried      : 1
% 7.78/2.76  
% 7.78/2.76  Timing (in seconds)
% 7.78/2.76  ----------------------
% 7.78/2.76  Preprocessing        : 0.40
% 7.78/2.76  Parsing              : 0.21
% 7.78/2.76  CNF conversion       : 0.03
% 7.78/2.76  Main loop            : 1.58
% 7.78/2.76  Inferencing          : 0.52
% 7.78/2.76  Reduction            : 0.53
% 7.78/2.76  Demodulation         : 0.38
% 7.78/2.76  BG Simplification    : 0.06
% 7.78/2.76  Subsumption          : 0.33
% 7.78/2.76  Abstraction          : 0.07
% 7.78/2.76  MUC search           : 0.00
% 7.78/2.76  Cooper               : 0.00
% 7.78/2.76  Total                : 2.03
% 7.78/2.76  Index Insertion      : 0.00
% 7.78/2.76  Index Deletion       : 0.00
% 7.78/2.76  Index Matching       : 0.00
% 7.78/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
