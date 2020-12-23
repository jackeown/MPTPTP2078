%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:01 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 186 expanded)
%              Number of leaves         :   36 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 367 expanded)
%              Number of equality atoms :   36 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_64,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_48,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_100,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_106,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_42])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_659,plain,(
    ! [B_92,A_93] :
      ( v2_tops_1(B_92,A_93)
      | ~ r1_tarski(B_92,k2_tops_1(A_93,B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_661,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_659])).

tff(c_663,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6,c_661])).

tff(c_36,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_819,plain,(
    ! [B_106,A_107] :
      ( v3_tops_1(B_106,A_107)
      | ~ v4_pre_topc(B_106,A_107)
      | ~ v2_tops_1(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_822,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_819])).

tff(c_825,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_663,c_36,c_822])).

tff(c_827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_825])).

tff(c_829,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_828,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1044,plain,(
    ! [B_140,A_141] :
      ( v2_tops_1(B_140,A_141)
      | ~ v3_tops_1(B_140,A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1047,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1044])).

tff(c_1050,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_828,c_1047])).

tff(c_1345,plain,(
    ! [B_158,A_159] :
      ( r1_tarski(B_158,k2_tops_1(A_159,B_158))
      | ~ v2_tops_1(B_158,A_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1347,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1345])).

tff(c_1350,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1050,c_1347])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_832,plain,(
    ! [A_108,B_109] : k1_setfam_1(k2_tarski(A_108,B_109)) = k3_xboole_0(B_109,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_20,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_838,plain,(
    ! [B_109,A_108] : k3_xboole_0(B_109,A_108) = k3_xboole_0(A_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_20])).

tff(c_983,plain,(
    ! [A_124,B_125,C_126] :
      ( k9_subset_1(A_124,B_125,C_126) = k3_xboole_0(B_125,C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_986,plain,(
    ! [B_125] : k9_subset_1(u1_struct_0('#skF_1'),B_125,'#skF_2') = k3_xboole_0(B_125,'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_983])).

tff(c_1008,plain,(
    ! [A_132,C_133,B_134] :
      ( k9_subset_1(A_132,C_133,B_134) = k9_subset_1(A_132,B_134,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1010,plain,(
    ! [B_134] : k9_subset_1(u1_struct_0('#skF_1'),B_134,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_134) ),
    inference(resolution,[status(thm)],[c_38,c_1008])).

tff(c_1012,plain,(
    ! [B_134] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_134) = k3_xboole_0(B_134,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_1010])).

tff(c_1058,plain,(
    ! [A_144,B_145] :
      ( k2_pre_topc(A_144,B_145) = B_145
      | ~ v4_pre_topc(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1061,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1058])).

tff(c_1064,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1061])).

tff(c_1557,plain,(
    ! [A_174,B_175] :
      ( k9_subset_1(u1_struct_0(A_174),k2_pre_topc(A_174,B_175),k2_pre_topc(A_174,k3_subset_1(u1_struct_0(A_174),B_175))) = k2_tops_1(A_174,B_175)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1566,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_1557])).

tff(c_1570,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_838,c_1012,c_1566])).

tff(c_914,plain,(
    ! [A_116,B_117] : k4_xboole_0(A_116,k4_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_932,plain,(
    ! [A_118,B_119] : r1_tarski(k3_xboole_0(A_118,B_119),A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_10])).

tff(c_942,plain,(
    ! [B_120,A_121] : r1_tarski(k3_xboole_0(B_120,A_121),A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_932])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1037,plain,(
    ! [B_138,A_139] :
      ( k3_xboole_0(B_138,A_139) = A_139
      | ~ r1_tarski(A_139,k3_xboole_0(B_138,A_139)) ) ),
    inference(resolution,[status(thm)],[c_942,c_2])).

tff(c_1040,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = B_109
      | ~ r1_tarski(B_109,k3_xboole_0(B_109,A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_1037])).

tff(c_1601,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1570,c_1040])).

tff(c_1633,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_1570,c_838,c_1601])).

tff(c_1635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_829,c_1633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:27:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.56  
% 3.50/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.56  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.50/1.56  
% 3.50/1.56  %Foreground sorts:
% 3.50/1.56  
% 3.50/1.56  
% 3.50/1.56  %Background operators:
% 3.50/1.56  
% 3.50/1.56  
% 3.50/1.56  %Foreground operators:
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.56  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.50/1.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.50/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.50/1.56  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.50/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.50/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.50/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.50/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.50/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.50/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.50/1.56  
% 3.68/1.58  tff(f_112, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.68/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.68/1.58  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.68/1.58  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 3.68/1.58  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.68/1.58  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.68/1.58  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.68/1.58  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.68/1.58  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.68/1.58  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.68/1.58  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 3.68/1.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.68/1.58  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.68/1.58  tff(c_48, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.58  tff(c_100, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 3.68/1.58  tff(c_42, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.58  tff(c_106, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_42])).
% 3.68/1.58  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.58  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.58  tff(c_659, plain, (![B_92, A_93]: (v2_tops_1(B_92, A_93) | ~r1_tarski(B_92, k2_tops_1(A_93, B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.68/1.58  tff(c_661, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_659])).
% 3.68/1.58  tff(c_663, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6, c_661])).
% 3.68/1.58  tff(c_36, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.68/1.58  tff(c_819, plain, (![B_106, A_107]: (v3_tops_1(B_106, A_107) | ~v4_pre_topc(B_106, A_107) | ~v2_tops_1(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.68/1.58  tff(c_822, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_819])).
% 3.68/1.58  tff(c_825, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_663, c_36, c_822])).
% 3.68/1.58  tff(c_827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_825])).
% 3.68/1.58  tff(c_829, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.68/1.58  tff(c_828, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.68/1.58  tff(c_1044, plain, (![B_140, A_141]: (v2_tops_1(B_140, A_141) | ~v3_tops_1(B_140, A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.68/1.58  tff(c_1047, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1044])).
% 3.68/1.58  tff(c_1050, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_828, c_1047])).
% 3.68/1.58  tff(c_1345, plain, (![B_158, A_159]: (r1_tarski(B_158, k2_tops_1(A_159, B_158)) | ~v2_tops_1(B_158, A_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.68/1.58  tff(c_1347, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1345])).
% 3.68/1.58  tff(c_1350, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1050, c_1347])).
% 3.68/1.58  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.58  tff(c_85, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.68/1.58  tff(c_832, plain, (![A_108, B_109]: (k1_setfam_1(k2_tarski(A_108, B_109))=k3_xboole_0(B_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_14, c_85])).
% 3.68/1.58  tff(c_20, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.68/1.58  tff(c_838, plain, (![B_109, A_108]: (k3_xboole_0(B_109, A_108)=k3_xboole_0(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_832, c_20])).
% 3.68/1.58  tff(c_983, plain, (![A_124, B_125, C_126]: (k9_subset_1(A_124, B_125, C_126)=k3_xboole_0(B_125, C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.68/1.58  tff(c_986, plain, (![B_125]: (k9_subset_1(u1_struct_0('#skF_1'), B_125, '#skF_2')=k3_xboole_0(B_125, '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_983])).
% 3.68/1.58  tff(c_1008, plain, (![A_132, C_133, B_134]: (k9_subset_1(A_132, C_133, B_134)=k9_subset_1(A_132, B_134, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.58  tff(c_1010, plain, (![B_134]: (k9_subset_1(u1_struct_0('#skF_1'), B_134, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_134))), inference(resolution, [status(thm)], [c_38, c_1008])).
% 3.68/1.58  tff(c_1012, plain, (![B_134]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_134)=k3_xboole_0(B_134, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_986, c_1010])).
% 3.68/1.58  tff(c_1058, plain, (![A_144, B_145]: (k2_pre_topc(A_144, B_145)=B_145 | ~v4_pre_topc(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.58  tff(c_1061, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1058])).
% 3.68/1.58  tff(c_1064, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1061])).
% 3.68/1.58  tff(c_1557, plain, (![A_174, B_175]: (k9_subset_1(u1_struct_0(A_174), k2_pre_topc(A_174, B_175), k2_pre_topc(A_174, k3_subset_1(u1_struct_0(A_174), B_175)))=k2_tops_1(A_174, B_175) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.68/1.58  tff(c_1566, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1064, c_1557])).
% 3.68/1.58  tff(c_1570, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_838, c_1012, c_1566])).
% 3.68/1.58  tff(c_914, plain, (![A_116, B_117]: (k4_xboole_0(A_116, k4_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.58  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.58  tff(c_932, plain, (![A_118, B_119]: (r1_tarski(k3_xboole_0(A_118, B_119), A_118))), inference(superposition, [status(thm), theory('equality')], [c_914, c_10])).
% 3.68/1.58  tff(c_942, plain, (![B_120, A_121]: (r1_tarski(k3_xboole_0(B_120, A_121), A_121))), inference(superposition, [status(thm), theory('equality')], [c_838, c_932])).
% 3.68/1.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.58  tff(c_1037, plain, (![B_138, A_139]: (k3_xboole_0(B_138, A_139)=A_139 | ~r1_tarski(A_139, k3_xboole_0(B_138, A_139)))), inference(resolution, [status(thm)], [c_942, c_2])).
% 3.68/1.58  tff(c_1040, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=B_109 | ~r1_tarski(B_109, k3_xboole_0(B_109, A_108)))), inference(superposition, [status(thm), theory('equality')], [c_838, c_1037])).
% 3.68/1.58  tff(c_1601, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1570, c_1040])).
% 3.68/1.58  tff(c_1633, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_1570, c_838, c_1601])).
% 3.68/1.58  tff(c_1635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_829, c_1633])).
% 3.68/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.58  
% 3.68/1.58  Inference rules
% 3.68/1.58  ----------------------
% 3.68/1.58  #Ref     : 0
% 3.68/1.58  #Sup     : 395
% 3.68/1.58  #Fact    : 0
% 3.68/1.58  #Define  : 0
% 3.68/1.58  #Split   : 1
% 3.68/1.58  #Chain   : 0
% 3.68/1.58  #Close   : 0
% 3.68/1.58  
% 3.68/1.58  Ordering : KBO
% 3.68/1.58  
% 3.68/1.58  Simplification rules
% 3.68/1.58  ----------------------
% 3.68/1.58  #Subsume      : 41
% 3.68/1.58  #Demod        : 219
% 3.68/1.58  #Tautology    : 207
% 3.68/1.58  #SimpNegUnit  : 3
% 3.68/1.58  #BackRed      : 0
% 3.68/1.58  
% 3.68/1.58  #Partial instantiations: 0
% 3.68/1.58  #Strategies tried      : 1
% 3.68/1.58  
% 3.68/1.58  Timing (in seconds)
% 3.68/1.58  ----------------------
% 3.68/1.58  Preprocessing        : 0.32
% 3.68/1.58  Parsing              : 0.17
% 3.68/1.58  CNF conversion       : 0.02
% 3.68/1.58  Main loop            : 0.48
% 3.68/1.58  Inferencing          : 0.16
% 3.68/1.58  Reduction            : 0.20
% 3.68/1.58  Demodulation         : 0.17
% 3.68/1.58  BG Simplification    : 0.02
% 3.68/1.58  Subsumption          : 0.07
% 3.68/1.58  Abstraction          : 0.03
% 3.68/1.58  MUC search           : 0.00
% 3.68/1.58  Cooper               : 0.00
% 3.68/1.58  Total                : 0.83
% 3.68/1.58  Index Insertion      : 0.00
% 3.68/1.58  Index Deletion       : 0.00
% 3.68/1.58  Index Matching       : 0.00
% 3.68/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
