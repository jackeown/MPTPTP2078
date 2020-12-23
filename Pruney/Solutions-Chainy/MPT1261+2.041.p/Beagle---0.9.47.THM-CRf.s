%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:17 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 510 expanded)
%              Number of leaves         :   42 ( 189 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 ( 942 expanded)
%              Number of equality atoms :   79 ( 346 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3739,plain,(
    ! [A_235,B_236] :
      ( r1_tarski(k1_tops_1(A_235,B_236),B_236)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ l1_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3744,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_3739])).

tff(c_3748,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3744])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3408,plain,(
    ! [A_210,B_211] :
      ( k4_xboole_0(A_210,B_211) = k3_subset_1(A_210,B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3415,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_3408])).

tff(c_3755,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3748,c_3415])).

tff(c_3424,plain,(
    ! [A_212,B_213,C_214] :
      ( k7_subset_1(A_212,B_213,C_214) = k4_xboole_0(B_213,C_214)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(A_212)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3430,plain,(
    ! [C_214] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_214) = k4_xboole_0('#skF_2',C_214) ),
    inference(resolution,[status(thm)],[c_42,c_3424])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_119,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1364,plain,(
    ! [B_130,A_131] :
      ( v4_pre_topc(B_130,A_131)
      | k2_pre_topc(A_131,B_130) != B_130
      | ~ v2_pre_topc(A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1374,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1364])).

tff(c_1379,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_1374])).

tff(c_1380,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_1379])).

tff(c_543,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_548,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_543])).

tff(c_552,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_548])).

tff(c_381,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_388,plain,(
    ! [C_77] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_77) = k4_xboole_0('#skF_2',C_77) ),
    inference(resolution,[status(thm)],[c_42,c_381])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_275,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_54])).

tff(c_394,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_275])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_406,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_4])).

tff(c_1183,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1442,plain,(
    ! [B_134,B_135,A_136] :
      ( k4_subset_1(B_134,B_135,A_136) = k2_xboole_0(B_135,A_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(B_134))
      | ~ r1_tarski(A_136,B_134) ) ),
    inference(resolution,[status(thm)],[c_26,c_1183])).

tff(c_1901,plain,(
    ! [B_145,A_146,A_147] :
      ( k4_subset_1(B_145,A_146,A_147) = k2_xboole_0(A_146,A_147)
      | ~ r1_tarski(A_147,B_145)
      | ~ r1_tarski(A_146,B_145) ) ),
    inference(resolution,[status(thm)],[c_26,c_1442])).

tff(c_2203,plain,(
    ! [A_158] :
      ( k4_subset_1('#skF_2',A_158,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(A_158,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_158,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_406,c_1901])).

tff(c_338,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_345,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_338])).

tff(c_557,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_552,c_345])).

tff(c_560,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_557])).

tff(c_12,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = k2_subset_1(A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_412,plain,(
    ! [A_78,B_79] :
      ( k4_subset_1(A_78,B_79,k3_subset_1(A_78,B_79)) = A_78
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_417,plain,(
    ! [B_25,A_24] :
      ( k4_subset_1(B_25,A_24,k3_subset_1(B_25,A_24)) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_412])).

tff(c_564,plain,
    ( k4_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_417])).

tff(c_568,plain,(
    k4_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_564])).

tff(c_2209,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_568])).

tff(c_2218,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_2209])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_213,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(B_63,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_219,plain,(
    ! [B_63,A_62] : k2_xboole_0(B_63,A_62) = k2_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_10])).

tff(c_236,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_10])).

tff(c_251,plain,(
    ! [A_65,B_64] : k2_xboole_0(A_65,k2_xboole_0(B_64,A_65)) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_6])).

tff(c_2260,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_251])).

tff(c_2274,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2260])).

tff(c_297,plain,(
    ! [A_68,B_69] : k2_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_6])).

tff(c_300,plain,(
    ! [B_69,A_68] : k2_xboole_0(k2_xboole_0(B_69,A_68),k2_xboole_0(A_68,B_69)) = k2_xboole_0(k2_xboole_0(B_69,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_251])).

tff(c_330,plain,(
    ! [B_69,A_68] : k2_xboole_0(k2_xboole_0(B_69,A_68),k2_xboole_0(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_219,c_300])).

tff(c_627,plain,(
    ! [B_95,A_96] : k2_xboole_0(k2_xboole_0(B_95,A_96),k2_xboole_0(A_96,B_95)) = k2_xboole_0(A_96,B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_219,c_300])).

tff(c_639,plain,(
    ! [A_96,B_95] : k2_xboole_0(k2_xboole_0(A_96,B_95),k2_xboole_0(B_95,A_96)) = k2_xboole_0(k2_xboole_0(A_96,B_95),k2_xboole_0(A_96,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_251])).

tff(c_691,plain,(
    ! [A_96,B_95] : k2_xboole_0(k2_xboole_0(A_96,B_95),k2_xboole_0(A_96,B_95)) = k2_xboole_0(B_95,A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_639])).

tff(c_2386,plain,(
    k2_xboole_0(k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2274,c_691])).

tff(c_2428,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_6,c_219,c_2218,c_219,c_2386])).

tff(c_1556,plain,(
    ! [A_138,B_139] :
      ( k4_subset_1(u1_struct_0(A_138),B_139,k2_tops_1(A_138,B_139)) = k2_pre_topc(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1563,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1556])).

tff(c_1568,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1563])).

tff(c_701,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k2_tops_1(A_97,B_98),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_718,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(k2_tops_1(A_97,B_98),u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_701,c_24])).

tff(c_1452,plain,(
    ! [A_137] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_137) = k2_xboole_0('#skF_2',A_137)
      | ~ r1_tarski(A_137,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1442])).

tff(c_1463,plain,(
    ! [B_98] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_98)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_718,c_1452])).

tff(c_3143,plain,(
    ! [B_189] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_189)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1463])).

tff(c_3154,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_3143])).

tff(c_3160,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_1568,c_3154])).

tff(c_3162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1380,c_3160])).

tff(c_3163,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3431,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3430,c_3163])).

tff(c_3756,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3755,c_3431])).

tff(c_3164,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3922,plain,(
    ! [A_239,B_240] :
      ( k2_pre_topc(A_239,B_240) = B_240
      | ~ v4_pre_topc(B_240,A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3929,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_3922])).

tff(c_3933,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3164,c_3929])).

tff(c_4898,plain,(
    ! [A_280,B_281] :
      ( k7_subset_1(u1_struct_0(A_280),k2_pre_topc(A_280,B_281),k1_tops_1(A_280,B_281)) = k2_tops_1(A_280,B_281)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4907,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3933,c_4898])).

tff(c_4911,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3755,c_3430,c_4907])).

tff(c_4913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3756,c_4911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.06  
% 5.64/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.07  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.64/2.07  
% 5.64/2.07  %Foreground sorts:
% 5.64/2.07  
% 5.64/2.07  
% 5.64/2.07  %Background operators:
% 5.64/2.07  
% 5.64/2.07  
% 5.64/2.07  %Foreground operators:
% 5.64/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.64/2.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.64/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.64/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.64/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.64/2.07  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.64/2.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.64/2.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.64/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.64/2.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.64/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.64/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.64/2.07  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.64/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.64/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.64/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.64/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.64/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.64/2.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.64/2.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.64/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.64/2.07  
% 5.78/2.09  tff(f_123, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.78/2.09  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.78/2.09  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.78/2.09  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.78/2.09  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.78/2.09  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.78/2.09  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.78/2.09  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.78/2.09  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.78/2.09  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.78/2.09  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.78/2.09  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.78/2.09  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.78/2.09  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.78/2.09  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.78/2.09  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.78/2.09  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.09  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.09  tff(c_3739, plain, (![A_235, B_236]: (r1_tarski(k1_tops_1(A_235, B_236), B_236) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(A_235))) | ~l1_pre_topc(A_235))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.78/2.09  tff(c_3744, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_3739])).
% 5.78/2.09  tff(c_3748, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3744])).
% 5.78/2.09  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.78/2.09  tff(c_3408, plain, (![A_210, B_211]: (k4_xboole_0(A_210, B_211)=k3_subset_1(A_210, B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(A_210)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.09  tff(c_3415, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_3408])).
% 5.78/2.09  tff(c_3755, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3748, c_3415])).
% 5.78/2.09  tff(c_3424, plain, (![A_212, B_213, C_214]: (k7_subset_1(A_212, B_213, C_214)=k4_xboole_0(B_213, C_214) | ~m1_subset_1(B_213, k1_zfmisc_1(A_212)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.78/2.09  tff(c_3430, plain, (![C_214]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_214)=k4_xboole_0('#skF_2', C_214))), inference(resolution, [status(thm)], [c_42, c_3424])).
% 5.78/2.09  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.09  tff(c_119, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 5.78/2.09  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.09  tff(c_1364, plain, (![B_130, A_131]: (v4_pre_topc(B_130, A_131) | k2_pre_topc(A_131, B_130)!=B_130 | ~v2_pre_topc(A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.78/2.09  tff(c_1374, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1364])).
% 5.78/2.09  tff(c_1379, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_1374])).
% 5.78/2.09  tff(c_1380, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_119, c_1379])).
% 5.78/2.09  tff(c_543, plain, (![A_91, B_92]: (r1_tarski(k1_tops_1(A_91, B_92), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.78/2.09  tff(c_548, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_543])).
% 5.78/2.09  tff(c_552, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_548])).
% 5.78/2.09  tff(c_381, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.78/2.09  tff(c_388, plain, (![C_77]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_77)=k4_xboole_0('#skF_2', C_77))), inference(resolution, [status(thm)], [c_42, c_381])).
% 5.78/2.09  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.09  tff(c_275, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_119, c_54])).
% 5.78/2.09  tff(c_394, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_388, c_275])).
% 5.78/2.09  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.78/2.09  tff(c_406, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_394, c_4])).
% 5.78/2.09  tff(c_1183, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.09  tff(c_1442, plain, (![B_134, B_135, A_136]: (k4_subset_1(B_134, B_135, A_136)=k2_xboole_0(B_135, A_136) | ~m1_subset_1(B_135, k1_zfmisc_1(B_134)) | ~r1_tarski(A_136, B_134))), inference(resolution, [status(thm)], [c_26, c_1183])).
% 5.78/2.09  tff(c_1901, plain, (![B_145, A_146, A_147]: (k4_subset_1(B_145, A_146, A_147)=k2_xboole_0(A_146, A_147) | ~r1_tarski(A_147, B_145) | ~r1_tarski(A_146, B_145))), inference(resolution, [status(thm)], [c_26, c_1442])).
% 5.78/2.09  tff(c_2203, plain, (![A_158]: (k4_subset_1('#skF_2', A_158, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(A_158, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_158, '#skF_2'))), inference(resolution, [status(thm)], [c_406, c_1901])).
% 5.78/2.09  tff(c_338, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.09  tff(c_345, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_338])).
% 5.78/2.09  tff(c_557, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_552, c_345])).
% 5.78/2.09  tff(c_560, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_557])).
% 5.78/2.09  tff(c_12, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.78/2.09  tff(c_20, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=k2_subset_1(A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.78/2.09  tff(c_412, plain, (![A_78, B_79]: (k4_subset_1(A_78, B_79, k3_subset_1(A_78, B_79))=A_78 | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 5.78/2.09  tff(c_417, plain, (![B_25, A_24]: (k4_subset_1(B_25, A_24, k3_subset_1(B_25, A_24))=B_25 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_412])).
% 5.78/2.09  tff(c_564, plain, (k4_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_560, c_417])).
% 5.78/2.09  tff(c_568, plain, (k4_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_552, c_564])).
% 5.78/2.09  tff(c_2209, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2203, c_568])).
% 5.78/2.09  tff(c_2218, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_552, c_2209])).
% 5.78/2.09  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.09  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.78/2.09  tff(c_125, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.78/2.09  tff(c_213, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_8, c_125])).
% 5.78/2.09  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.78/2.09  tff(c_219, plain, (![B_63, A_62]: (k2_xboole_0(B_63, A_62)=k2_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_213, c_10])).
% 5.78/2.09  tff(c_236, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_213, c_10])).
% 5.78/2.09  tff(c_251, plain, (![A_65, B_64]: (k2_xboole_0(A_65, k2_xboole_0(B_64, A_65))=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_236, c_6])).
% 5.78/2.09  tff(c_2260, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2218, c_251])).
% 5.78/2.09  tff(c_2274, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2260])).
% 5.78/2.09  tff(c_297, plain, (![A_68, B_69]: (k2_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_236, c_6])).
% 5.78/2.09  tff(c_300, plain, (![B_69, A_68]: (k2_xboole_0(k2_xboole_0(B_69, A_68), k2_xboole_0(A_68, B_69))=k2_xboole_0(k2_xboole_0(B_69, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_297, c_251])).
% 5.78/2.09  tff(c_330, plain, (![B_69, A_68]: (k2_xboole_0(k2_xboole_0(B_69, A_68), k2_xboole_0(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_219, c_300])).
% 5.78/2.09  tff(c_627, plain, (![B_95, A_96]: (k2_xboole_0(k2_xboole_0(B_95, A_96), k2_xboole_0(A_96, B_95))=k2_xboole_0(A_96, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_219, c_300])).
% 5.78/2.09  tff(c_639, plain, (![A_96, B_95]: (k2_xboole_0(k2_xboole_0(A_96, B_95), k2_xboole_0(B_95, A_96))=k2_xboole_0(k2_xboole_0(A_96, B_95), k2_xboole_0(A_96, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_627, c_251])).
% 5.78/2.09  tff(c_691, plain, (![A_96, B_95]: (k2_xboole_0(k2_xboole_0(A_96, B_95), k2_xboole_0(A_96, B_95))=k2_xboole_0(B_95, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_639])).
% 5.78/2.09  tff(c_2386, plain, (k2_xboole_0(k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2274, c_691])).
% 5.78/2.09  tff(c_2428, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_6, c_219, c_2218, c_219, c_2386])).
% 5.78/2.09  tff(c_1556, plain, (![A_138, B_139]: (k4_subset_1(u1_struct_0(A_138), B_139, k2_tops_1(A_138, B_139))=k2_pre_topc(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.78/2.09  tff(c_1563, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1556])).
% 5.78/2.09  tff(c_1568, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1563])).
% 5.78/2.09  tff(c_701, plain, (![A_97, B_98]: (m1_subset_1(k2_tops_1(A_97, B_98), k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.78/2.09  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.78/2.09  tff(c_718, plain, (![A_97, B_98]: (r1_tarski(k2_tops_1(A_97, B_98), u1_struct_0(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_701, c_24])).
% 5.78/2.09  tff(c_1452, plain, (![A_137]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_137)=k2_xboole_0('#skF_2', A_137) | ~r1_tarski(A_137, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_1442])).
% 5.78/2.09  tff(c_1463, plain, (![B_98]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_98))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_718, c_1452])).
% 5.78/2.09  tff(c_3143, plain, (![B_189]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_189))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1463])).
% 5.78/2.09  tff(c_3154, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_3143])).
% 5.78/2.09  tff(c_3160, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2428, c_1568, c_3154])).
% 5.78/2.09  tff(c_3162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1380, c_3160])).
% 5.78/2.09  tff(c_3163, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.78/2.09  tff(c_3431, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3430, c_3163])).
% 5.78/2.09  tff(c_3756, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3755, c_3431])).
% 5.78/2.09  tff(c_3164, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 5.78/2.09  tff(c_3922, plain, (![A_239, B_240]: (k2_pre_topc(A_239, B_240)=B_240 | ~v4_pre_topc(B_240, A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.78/2.09  tff(c_3929, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_3922])).
% 5.78/2.09  tff(c_3933, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3164, c_3929])).
% 5.78/2.09  tff(c_4898, plain, (![A_280, B_281]: (k7_subset_1(u1_struct_0(A_280), k2_pre_topc(A_280, B_281), k1_tops_1(A_280, B_281))=k2_tops_1(A_280, B_281) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.78/2.09  tff(c_4907, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3933, c_4898])).
% 5.78/2.09  tff(c_4911, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3755, c_3430, c_4907])).
% 5.78/2.09  tff(c_4913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3756, c_4911])).
% 5.78/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.09  
% 5.78/2.09  Inference rules
% 5.78/2.09  ----------------------
% 5.78/2.09  #Ref     : 0
% 5.78/2.09  #Sup     : 1191
% 5.78/2.09  #Fact    : 0
% 5.78/2.09  #Define  : 0
% 5.78/2.09  #Split   : 3
% 5.78/2.09  #Chain   : 0
% 5.78/2.09  #Close   : 0
% 5.78/2.09  
% 5.78/2.09  Ordering : KBO
% 5.78/2.09  
% 5.78/2.09  Simplification rules
% 5.78/2.09  ----------------------
% 5.78/2.09  #Subsume      : 69
% 5.78/2.09  #Demod        : 1183
% 5.78/2.09  #Tautology    : 639
% 5.78/2.09  #SimpNegUnit  : 6
% 5.78/2.09  #BackRed      : 4
% 5.78/2.09  
% 5.78/2.09  #Partial instantiations: 0
% 5.78/2.09  #Strategies tried      : 1
% 5.78/2.09  
% 5.78/2.09  Timing (in seconds)
% 5.78/2.09  ----------------------
% 5.78/2.09  Preprocessing        : 0.33
% 5.78/2.09  Parsing              : 0.17
% 5.78/2.09  CNF conversion       : 0.02
% 5.78/2.09  Main loop            : 0.99
% 5.78/2.09  Inferencing          : 0.30
% 5.78/2.09  Reduction            : 0.44
% 5.78/2.09  Demodulation         : 0.36
% 5.78/2.09  BG Simplification    : 0.04
% 5.78/2.09  Subsumption          : 0.14
% 5.78/2.09  Abstraction          : 0.06
% 5.78/2.09  MUC search           : 0.00
% 5.78/2.09  Cooper               : 0.00
% 5.78/2.09  Total                : 1.37
% 5.78/2.09  Index Insertion      : 0.00
% 5.78/2.09  Index Deletion       : 0.00
% 5.78/2.09  Index Matching       : 0.00
% 5.78/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
