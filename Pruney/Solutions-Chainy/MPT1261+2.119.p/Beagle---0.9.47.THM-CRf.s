%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:28 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 151 expanded)
%              Number of leaves         :   42 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 277 expanded)
%              Number of equality atoms :   44 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2015,plain,(
    ! [A_267,B_268,C_269] :
      ( k7_subset_1(A_267,B_268,C_269) = k4_xboole_0(B_268,C_269)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(A_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2026,plain,(
    ! [C_269] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_269) = k4_xboole_0('#skF_2',C_269) ),
    inference(resolution,[status(thm)],[c_48,c_2015])).

tff(c_54,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_116,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1009,plain,(
    ! [B_167,A_168] :
      ( v4_pre_topc(B_167,A_168)
      | k2_pre_topc(A_168,B_167) != B_167
      | ~ v2_pre_topc(A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1039,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1009])).

tff(c_1063,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1039])).

tff(c_1064,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_1063])).

tff(c_1215,plain,(
    ! [A_183,B_184] :
      ( k4_subset_1(u1_struct_0(A_183),B_184,k2_tops_1(A_183,B_184)) = k2_pre_topc(A_183,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1236,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1215])).

tff(c_1258,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1236])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_184,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_subset_1(A_84,B_85,C_86) = k4_xboole_0(B_85,C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    ! [C_89] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_89) = k4_xboole_0('#skF_2',C_89) ),
    inference(resolution,[status(thm)],[c_48,c_184])).

tff(c_60,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_179,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_60])).

tff(c_209,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_179])).

tff(c_20,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_35] : m1_subset_1(k2_subset_1(A_35),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    ! [A_35] : m1_subset_1(A_35,k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_193,plain,(
    ! [A_35,C_86] : k7_subset_1(A_35,A_35,C_86) = k4_xboole_0(A_35,C_86) ),
    inference(resolution,[status(thm)],[c_61,c_184])).

tff(c_223,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k7_subset_1(A_90,B_91,C_92),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_234,plain,(
    ! [A_35,C_86] :
      ( m1_subset_1(k4_xboole_0(A_35,C_86),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(A_35,k1_zfmisc_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_223])).

tff(c_246,plain,(
    ! [A_93,C_94] : m1_subset_1(k4_xboole_0(A_93,C_94),k1_zfmisc_1(A_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_234])).

tff(c_32,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [A_95,C_96] : r1_tarski(k4_xboole_0(A_95,C_96),A_95) ),
    inference(resolution,[status(thm)],[c_246,c_32])).

tff(c_263,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_257])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_268,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_263,c_6])).

tff(c_340,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_268])).

tff(c_237,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_223])).

tff(c_245,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_237])).

tff(c_358,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_245,c_32])).

tff(c_34,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_836,plain,(
    ! [A_158,B_159,C_160] :
      ( k4_subset_1(A_158,B_159,C_160) = k2_xboole_0(B_159,C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(A_158))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1780,plain,(
    ! [B_238,B_239,A_240] :
      ( k4_subset_1(B_238,B_239,A_240) = k2_xboole_0(B_239,A_240)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(B_238))
      | ~ r1_tarski(A_240,B_238) ) ),
    inference(resolution,[status(thm)],[c_34,c_836])).

tff(c_1879,plain,(
    ! [A_245] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_245) = k2_xboole_0('#skF_2',A_245)
      | ~ r1_tarski(A_245,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1780])).

tff(c_1903,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_358,c_1879])).

tff(c_1927,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_340,c_1903])).

tff(c_1929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1064,c_1927])).

tff(c_1930,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2070,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_1930])).

tff(c_1931,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2294,plain,(
    ! [A_311,B_312] :
      ( k2_pre_topc(A_311,B_312) = B_312
      | ~ v4_pre_topc(B_312,A_311)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2318,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2294])).

tff(c_2335,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1931,c_2318])).

tff(c_3172,plain,(
    ! [A_413,B_414] :
      ( k7_subset_1(u1_struct_0(A_413),k2_pre_topc(A_413,B_414),k1_tops_1(A_413,B_414)) = k2_tops_1(A_413,B_414)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3190,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2335,c_3172])).

tff(c_3194,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2026,c_3190])).

tff(c_3196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2070,c_3194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.89  
% 4.55/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.89  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.55/1.89  
% 4.55/1.89  %Foreground sorts:
% 4.55/1.89  
% 4.55/1.89  
% 4.55/1.89  %Background operators:
% 4.55/1.89  
% 4.55/1.89  
% 4.55/1.89  %Foreground operators:
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.55/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.55/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/1.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.55/1.89  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.55/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.89  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.55/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.55/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.55/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.55/1.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.55/1.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.55/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.55/1.89  
% 4.55/1.91  tff(f_124, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 4.55/1.91  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.55/1.91  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.55/1.91  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.55/1.91  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.55/1.91  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.55/1.91  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.55/1.91  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.55/1.91  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.55/1.91  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.55/1.91  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.55/1.91  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.55/1.91  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.55/1.91  tff(c_2015, plain, (![A_267, B_268, C_269]: (k7_subset_1(A_267, B_268, C_269)=k4_xboole_0(B_268, C_269) | ~m1_subset_1(B_268, k1_zfmisc_1(A_267)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.91  tff(c_2026, plain, (![C_269]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_269)=k4_xboole_0('#skF_2', C_269))), inference(resolution, [status(thm)], [c_48, c_2015])).
% 4.55/1.91  tff(c_54, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.55/1.91  tff(c_116, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 4.55/1.91  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.55/1.91  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.55/1.91  tff(c_1009, plain, (![B_167, A_168]: (v4_pre_topc(B_167, A_168) | k2_pre_topc(A_168, B_167)!=B_167 | ~v2_pre_topc(A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.91  tff(c_1039, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1009])).
% 4.55/1.91  tff(c_1063, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1039])).
% 4.55/1.91  tff(c_1064, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_116, c_1063])).
% 4.55/1.91  tff(c_1215, plain, (![A_183, B_184]: (k4_subset_1(u1_struct_0(A_183), B_184, k2_tops_1(A_183, B_184))=k2_pre_topc(A_183, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.55/1.91  tff(c_1236, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1215])).
% 4.55/1.91  tff(c_1258, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1236])).
% 4.55/1.91  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.91  tff(c_184, plain, (![A_84, B_85, C_86]: (k7_subset_1(A_84, B_85, C_86)=k4_xboole_0(B_85, C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.91  tff(c_203, plain, (![C_89]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_89)=k4_xboole_0('#skF_2', C_89))), inference(resolution, [status(thm)], [c_48, c_184])).
% 4.55/1.91  tff(c_60, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.55/1.91  tff(c_179, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_116, c_60])).
% 4.55/1.91  tff(c_209, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_203, c_179])).
% 4.55/1.91  tff(c_20, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.91  tff(c_22, plain, (![A_35]: (m1_subset_1(k2_subset_1(A_35), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.55/1.91  tff(c_61, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 4.55/1.91  tff(c_193, plain, (![A_35, C_86]: (k7_subset_1(A_35, A_35, C_86)=k4_xboole_0(A_35, C_86))), inference(resolution, [status(thm)], [c_61, c_184])).
% 4.55/1.91  tff(c_223, plain, (![A_90, B_91, C_92]: (m1_subset_1(k7_subset_1(A_90, B_91, C_92), k1_zfmisc_1(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.55/1.91  tff(c_234, plain, (![A_35, C_86]: (m1_subset_1(k4_xboole_0(A_35, C_86), k1_zfmisc_1(A_35)) | ~m1_subset_1(A_35, k1_zfmisc_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_223])).
% 4.55/1.91  tff(c_246, plain, (![A_93, C_94]: (m1_subset_1(k4_xboole_0(A_93, C_94), k1_zfmisc_1(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_234])).
% 4.55/1.91  tff(c_32, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.91  tff(c_257, plain, (![A_95, C_96]: (r1_tarski(k4_xboole_0(A_95, C_96), A_95))), inference(resolution, [status(thm)], [c_246, c_32])).
% 4.55/1.91  tff(c_263, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_209, c_257])).
% 4.55/1.91  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.91  tff(c_268, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_263, c_6])).
% 4.55/1.91  tff(c_340, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_268])).
% 4.55/1.91  tff(c_237, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_179, c_223])).
% 4.55/1.91  tff(c_245, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_237])).
% 4.55/1.91  tff(c_358, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_245, c_32])).
% 4.55/1.91  tff(c_34, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.91  tff(c_836, plain, (![A_158, B_159, C_160]: (k4_subset_1(A_158, B_159, C_160)=k2_xboole_0(B_159, C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(A_158)) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.55/1.91  tff(c_1780, plain, (![B_238, B_239, A_240]: (k4_subset_1(B_238, B_239, A_240)=k2_xboole_0(B_239, A_240) | ~m1_subset_1(B_239, k1_zfmisc_1(B_238)) | ~r1_tarski(A_240, B_238))), inference(resolution, [status(thm)], [c_34, c_836])).
% 4.55/1.91  tff(c_1879, plain, (![A_245]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_245)=k2_xboole_0('#skF_2', A_245) | ~r1_tarski(A_245, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_48, c_1780])).
% 4.55/1.91  tff(c_1903, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_358, c_1879])).
% 4.55/1.91  tff(c_1927, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_340, c_1903])).
% 4.55/1.91  tff(c_1929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1064, c_1927])).
% 4.55/1.91  tff(c_1930, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 4.55/1.91  tff(c_2070, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_1930])).
% 4.55/1.91  tff(c_1931, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 4.55/1.91  tff(c_2294, plain, (![A_311, B_312]: (k2_pre_topc(A_311, B_312)=B_312 | ~v4_pre_topc(B_312, A_311) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.91  tff(c_2318, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2294])).
% 4.55/1.91  tff(c_2335, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1931, c_2318])).
% 4.55/1.91  tff(c_3172, plain, (![A_413, B_414]: (k7_subset_1(u1_struct_0(A_413), k2_pre_topc(A_413, B_414), k1_tops_1(A_413, B_414))=k2_tops_1(A_413, B_414) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.55/1.91  tff(c_3190, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2335, c_3172])).
% 4.55/1.91  tff(c_3194, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2026, c_3190])).
% 4.55/1.91  tff(c_3196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2070, c_3194])).
% 4.55/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.91  
% 4.55/1.91  Inference rules
% 4.55/1.91  ----------------------
% 4.55/1.91  #Ref     : 0
% 4.55/1.91  #Sup     : 737
% 4.55/1.91  #Fact    : 0
% 4.55/1.91  #Define  : 0
% 4.55/1.91  #Split   : 2
% 4.55/1.91  #Chain   : 0
% 4.55/1.91  #Close   : 0
% 4.55/1.91  
% 4.55/1.91  Ordering : KBO
% 4.55/1.91  
% 4.55/1.91  Simplification rules
% 4.55/1.91  ----------------------
% 4.55/1.91  #Subsume      : 15
% 4.55/1.91  #Demod        : 424
% 4.55/1.91  #Tautology    : 376
% 4.55/1.91  #SimpNegUnit  : 8
% 4.55/1.91  #BackRed      : 4
% 4.55/1.91  
% 4.55/1.91  #Partial instantiations: 0
% 4.55/1.91  #Strategies tried      : 1
% 4.55/1.91  
% 4.55/1.91  Timing (in seconds)
% 4.55/1.91  ----------------------
% 4.96/1.91  Preprocessing        : 0.35
% 4.96/1.91  Parsing              : 0.19
% 4.96/1.91  CNF conversion       : 0.02
% 4.96/1.91  Main loop            : 0.78
% 4.96/1.91  Inferencing          : 0.27
% 4.96/1.91  Reduction            : 0.29
% 4.96/1.91  Demodulation         : 0.21
% 4.96/1.91  BG Simplification    : 0.04
% 4.96/1.91  Subsumption          : 0.13
% 4.96/1.91  Abstraction          : 0.04
% 4.96/1.91  MUC search           : 0.00
% 4.96/1.91  Cooper               : 0.00
% 4.96/1.91  Total                : 1.16
% 4.96/1.91  Index Insertion      : 0.00
% 4.96/1.91  Index Deletion       : 0.00
% 4.96/1.91  Index Matching       : 0.00
% 4.96/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
