%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 8.98s
% Output     : CNFRefutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 286 expanded)
%              Number of leaves         :   45 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  187 ( 538 expanded)
%              Number of equality atoms :   91 ( 187 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_95,axiom,(
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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14747,plain,(
    ! [A_444,B_445] :
      ( r1_tarski(k1_tops_1(A_444,B_445),B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14761,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_14747])).

tff(c_14768,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14761])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14314,plain,(
    ! [A_418,B_419] :
      ( k4_xboole_0(A_418,B_419) = k3_subset_1(A_418,B_419)
      | ~ m1_subset_1(B_419,k1_zfmisc_1(A_418)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14325,plain,(
    ! [B_36,A_35] :
      ( k4_xboole_0(B_36,A_35) = k3_subset_1(B_36,A_35)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_14314])).

tff(c_14772,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14768,c_14325])).

tff(c_14647,plain,(
    ! [A_435,B_436,C_437] :
      ( k7_subset_1(A_435,B_436,C_437) = k4_xboole_0(B_436,C_437)
      | ~ m1_subset_1(B_436,k1_zfmisc_1(A_435)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14656,plain,(
    ! [C_437] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_437) = k4_xboole_0('#skF_2',C_437) ),
    inference(resolution,[status(thm)],[c_52,c_14647])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_246,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2015,plain,(
    ! [B_160,A_161] :
      ( v4_pre_topc(B_160,A_161)
      | k2_pre_topc(A_161,B_160) != B_160
      | ~ v2_pre_topc(A_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2037,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2015])).

tff(c_2045,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_2037])).

tff(c_2046,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_2045])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_191,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_179])).

tff(c_194,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_191])).

tff(c_304,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_322,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_304])).

tff(c_325,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_322])).

tff(c_100,plain,(
    ! [A_57,B_58] : r1_tarski(k4_xboole_0(A_57,B_58),A_57) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_805,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = k3_subset_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_877,plain,(
    ! [B_111,A_112] :
      ( k4_xboole_0(B_111,A_112) = k3_subset_1(B_111,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(resolution,[status(thm)],[c_36,c_805])).

tff(c_898,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_subset_1(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_103,c_877])).

tff(c_912,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_898])).

tff(c_1006,plain,(
    ! [A_117,B_118,C_119] :
      ( k7_subset_1(A_117,B_118,C_119) = k4_xboole_0(B_118,C_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1061,plain,(
    ! [C_120] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_120) = k4_xboole_0('#skF_2',C_120) ),
    inference(resolution,[status(thm)],[c_52,c_1006])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_138,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1067,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_138])).

tff(c_1123,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(k1_tops_1(A_122,B_123),B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1131,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1123])).

tff(c_1136,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1131])).

tff(c_816,plain,(
    ! [B_36,A_35] :
      ( k4_xboole_0(B_36,A_35) = k3_subset_1(B_36,A_35)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_805])).

tff(c_1163,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1136,c_816])).

tff(c_1165,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_1163])).

tff(c_571,plain,(
    ! [A_94,B_95] :
      ( k3_subset_1(A_94,k3_subset_1(A_94,B_95)) = B_95
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_576,plain,(
    ! [B_36,A_35] :
      ( k3_subset_1(B_36,k3_subset_1(B_36,A_35)) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_571])).

tff(c_1186,plain,
    ( k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_576])).

tff(c_1196,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_1186])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_901,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_subset_1(A_6,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_8,c_877])).

tff(c_914,plain,(
    ! [A_6,B_7] : k3_subset_1(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_901])).

tff(c_1079,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_914])).

tff(c_1512,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_1079])).

tff(c_307,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,k4_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_12])).

tff(c_1517,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1512,c_307])).

tff(c_1538,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_1067,c_1517])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_281,plain,(
    ! [A_78,B_79] : k1_setfam_1(k2_tarski(A_78,B_79)) = k3_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_139])).

tff(c_32,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_287,plain,(
    ! [B_79,A_78] : k3_xboole_0(B_79,A_78) = k3_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_32])).

tff(c_966,plain,(
    ! [A_115,B_116] : k3_subset_1(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_901])).

tff(c_972,plain,(
    ! [A_115,B_116] :
      ( k3_subset_1(A_115,k3_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116)
      | ~ r1_tarski(k4_xboole_0(A_115,B_116),A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_576])).

tff(c_1199,plain,(
    ! [A_128,B_129] : k3_subset_1(A_128,k3_xboole_0(A_128,B_129)) = k4_xboole_0(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_972])).

tff(c_1226,plain,(
    ! [B_79,A_78] : k3_subset_1(B_79,k3_xboole_0(A_78,B_79)) = k4_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_1199])).

tff(c_1597,plain,(
    k3_subset_1(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_1226])).

tff(c_1616,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_1597])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1654,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1616,c_14])).

tff(c_1664,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_1654])).

tff(c_2595,plain,(
    ! [A_178,B_179] :
      ( k4_subset_1(u1_struct_0(A_178),B_179,k2_tops_1(A_178,B_179)) = k2_pre_topc(A_178,B_179)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2611,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2595])).

tff(c_2619,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2611])).

tff(c_42,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k2_tops_1(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1732,plain,(
    ! [A_147,B_148,C_149] :
      ( k4_subset_1(A_147,B_148,C_149) = k2_xboole_0(B_148,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_13217,plain,(
    ! [A_361,B_362,B_363] :
      ( k4_subset_1(u1_struct_0(A_361),B_362,k2_tops_1(A_361,B_363)) = k2_xboole_0(B_362,k2_tops_1(A_361,B_363))
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(resolution,[status(thm)],[c_42,c_1732])).

tff(c_13235,plain,(
    ! [B_363] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_363)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_363))
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_13217])).

tff(c_13467,plain,(
    ! [B_368] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_368)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_368))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_13235])).

tff(c_13493,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_13467])).

tff(c_13503,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_2619,c_13493])).

tff(c_13505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2046,c_13503])).

tff(c_13506,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_13813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13506,c_138])).

tff(c_13814,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_13913,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13814,c_58])).

tff(c_14657,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14656,c_13913])).

tff(c_14798,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14772,c_14657])).

tff(c_14920,plain,(
    ! [A_454,B_455] :
      ( k2_pre_topc(A_454,B_455) = B_455
      | ~ v4_pre_topc(B_455,A_454)
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14939,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_14920])).

tff(c_14946,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_13814,c_14939])).

tff(c_17148,plain,(
    ! [A_519,B_520] :
      ( k7_subset_1(u1_struct_0(A_519),k2_pre_topc(A_519,B_520),k1_tops_1(A_519,B_520)) = k2_tops_1(A_519,B_520)
      | ~ m1_subset_1(B_520,k1_zfmisc_1(u1_struct_0(A_519)))
      | ~ l1_pre_topc(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_17157,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14946,c_17148])).

tff(c_17161,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_14772,c_14656,c_17157])).

tff(c_17163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14798,c_17161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:19:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.98/3.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/3.31  
% 8.98/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/3.31  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.98/3.31  
% 8.98/3.31  %Foreground sorts:
% 8.98/3.31  
% 8.98/3.31  
% 8.98/3.31  %Background operators:
% 8.98/3.31  
% 8.98/3.31  
% 8.98/3.31  %Foreground operators:
% 8.98/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.98/3.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.98/3.31  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.98/3.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.98/3.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.98/3.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.98/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.98/3.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.98/3.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.98/3.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.98/3.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.98/3.31  tff('#skF_2', type, '#skF_2': $i).
% 8.98/3.31  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.98/3.31  tff('#skF_1', type, '#skF_1': $i).
% 8.98/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.98/3.31  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.98/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.98/3.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.98/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.98/3.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.98/3.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.98/3.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.98/3.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.98/3.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.98/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.98/3.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.98/3.31  
% 9.16/3.33  tff(f_142, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 9.16/3.33  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 9.16/3.33  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.16/3.33  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.16/3.33  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.16/3.33  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.16/3.33  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.16/3.33  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.16/3.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.16/3.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.16/3.33  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.16/3.33  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.16/3.33  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.16/3.33  tff(f_76, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.16/3.33  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.16/3.33  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 9.16/3.33  tff(f_101, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.16/3.33  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.16/3.33  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 9.16/3.33  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.16/3.33  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.16/3.33  tff(c_14747, plain, (![A_444, B_445]: (r1_tarski(k1_tops_1(A_444, B_445), B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.16/3.33  tff(c_14761, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_14747])).
% 9.16/3.33  tff(c_14768, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14761])).
% 9.16/3.33  tff(c_36, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.16/3.33  tff(c_14314, plain, (![A_418, B_419]: (k4_xboole_0(A_418, B_419)=k3_subset_1(A_418, B_419) | ~m1_subset_1(B_419, k1_zfmisc_1(A_418)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.16/3.33  tff(c_14325, plain, (![B_36, A_35]: (k4_xboole_0(B_36, A_35)=k3_subset_1(B_36, A_35) | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_36, c_14314])).
% 9.16/3.33  tff(c_14772, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14768, c_14325])).
% 9.16/3.33  tff(c_14647, plain, (![A_435, B_436, C_437]: (k7_subset_1(A_435, B_436, C_437)=k4_xboole_0(B_436, C_437) | ~m1_subset_1(B_436, k1_zfmisc_1(A_435)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.16/3.33  tff(c_14656, plain, (![C_437]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_437)=k4_xboole_0('#skF_2', C_437))), inference(resolution, [status(thm)], [c_52, c_14647])).
% 9.16/3.33  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.16/3.33  tff(c_246, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 9.16/3.33  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.16/3.33  tff(c_2015, plain, (![B_160, A_161]: (v4_pre_topc(B_160, A_161) | k2_pre_topc(A_161, B_160)!=B_160 | ~v2_pre_topc(A_161) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.16/3.33  tff(c_2037, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2015])).
% 9.16/3.33  tff(c_2045, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_2037])).
% 9.16/3.33  tff(c_2046, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_246, c_2045])).
% 9.16/3.33  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.16/3.33  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.16/3.33  tff(c_179, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.16/3.33  tff(c_191, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_179])).
% 9.16/3.33  tff(c_194, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_191])).
% 9.16/3.33  tff(c_304, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.16/3.33  tff(c_322, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_304])).
% 9.16/3.33  tff(c_325, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_322])).
% 9.16/3.33  tff(c_100, plain, (![A_57, B_58]: (r1_tarski(k4_xboole_0(A_57, B_58), A_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.33  tff(c_103, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 9.16/3.33  tff(c_805, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=k3_subset_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.16/3.33  tff(c_877, plain, (![B_111, A_112]: (k4_xboole_0(B_111, A_112)=k3_subset_1(B_111, A_112) | ~r1_tarski(A_112, B_111))), inference(resolution, [status(thm)], [c_36, c_805])).
% 9.16/3.33  tff(c_898, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_subset_1(A_8, A_8))), inference(resolution, [status(thm)], [c_103, c_877])).
% 9.16/3.33  tff(c_912, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_325, c_898])).
% 9.16/3.33  tff(c_1006, plain, (![A_117, B_118, C_119]: (k7_subset_1(A_117, B_118, C_119)=k4_xboole_0(B_118, C_119) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.16/3.33  tff(c_1061, plain, (![C_120]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_120)=k4_xboole_0('#skF_2', C_120))), inference(resolution, [status(thm)], [c_52, c_1006])).
% 9.16/3.33  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.16/3.33  tff(c_138, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 9.16/3.33  tff(c_1067, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1061, c_138])).
% 9.16/3.33  tff(c_1123, plain, (![A_122, B_123]: (r1_tarski(k1_tops_1(A_122, B_123), B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.16/3.33  tff(c_1131, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1123])).
% 9.16/3.33  tff(c_1136, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1131])).
% 9.16/3.33  tff(c_816, plain, (![B_36, A_35]: (k4_xboole_0(B_36, A_35)=k3_subset_1(B_36, A_35) | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_36, c_805])).
% 9.16/3.33  tff(c_1163, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1136, c_816])).
% 9.16/3.33  tff(c_1165, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_1163])).
% 9.16/3.33  tff(c_571, plain, (![A_94, B_95]: (k3_subset_1(A_94, k3_subset_1(A_94, B_95))=B_95 | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.16/3.33  tff(c_576, plain, (![B_36, A_35]: (k3_subset_1(B_36, k3_subset_1(B_36, A_35))=A_35 | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_36, c_571])).
% 9.16/3.33  tff(c_1186, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1165, c_576])).
% 9.16/3.33  tff(c_1196, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_1186])).
% 9.16/3.33  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.16/3.33  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.33  tff(c_901, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_subset_1(A_6, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_8, c_877])).
% 9.16/3.33  tff(c_914, plain, (![A_6, B_7]: (k3_subset_1(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_901])).
% 9.16/3.33  tff(c_1079, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_914])).
% 9.16/3.33  tff(c_1512, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_1079])).
% 9.16/3.33  tff(c_307, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k3_xboole_0(A_80, k4_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_304, c_12])).
% 9.16/3.33  tff(c_1517, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1512, c_307])).
% 9.16/3.33  tff(c_1538, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_1067, c_1517])).
% 9.16/3.33  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.16/3.33  tff(c_139, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.16/3.33  tff(c_281, plain, (![A_78, B_79]: (k1_setfam_1(k2_tarski(A_78, B_79))=k3_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_16, c_139])).
% 9.16/3.33  tff(c_32, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.16/3.33  tff(c_287, plain, (![B_79, A_78]: (k3_xboole_0(B_79, A_78)=k3_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_281, c_32])).
% 9.16/3.33  tff(c_966, plain, (![A_115, B_116]: (k3_subset_1(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_901])).
% 9.16/3.33  tff(c_972, plain, (![A_115, B_116]: (k3_subset_1(A_115, k3_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116) | ~r1_tarski(k4_xboole_0(A_115, B_116), A_115))), inference(superposition, [status(thm), theory('equality')], [c_966, c_576])).
% 9.16/3.33  tff(c_1199, plain, (![A_128, B_129]: (k3_subset_1(A_128, k3_xboole_0(A_128, B_129))=k4_xboole_0(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_972])).
% 9.16/3.33  tff(c_1226, plain, (![B_79, A_78]: (k3_subset_1(B_79, k3_xboole_0(A_78, B_79))=k4_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_287, c_1199])).
% 9.16/3.33  tff(c_1597, plain, (k3_subset_1(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1538, c_1226])).
% 9.16/3.33  tff(c_1616, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_912, c_1597])).
% 9.16/3.33  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.16/3.33  tff(c_1654, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1616, c_14])).
% 9.16/3.33  tff(c_1664, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_1654])).
% 9.16/3.33  tff(c_2595, plain, (![A_178, B_179]: (k4_subset_1(u1_struct_0(A_178), B_179, k2_tops_1(A_178, B_179))=k2_pre_topc(A_178, B_179) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.16/3.33  tff(c_2611, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2595])).
% 9.16/3.33  tff(c_2619, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2611])).
% 9.16/3.33  tff(c_42, plain, (![A_40, B_41]: (m1_subset_1(k2_tops_1(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.16/3.33  tff(c_1732, plain, (![A_147, B_148, C_149]: (k4_subset_1(A_147, B_148, C_149)=k2_xboole_0(B_148, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(A_147)) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.16/3.33  tff(c_13217, plain, (![A_361, B_362, B_363]: (k4_subset_1(u1_struct_0(A_361), B_362, k2_tops_1(A_361, B_363))=k2_xboole_0(B_362, k2_tops_1(A_361, B_363)) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(A_361))) | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_pre_topc(A_361))), inference(resolution, [status(thm)], [c_42, c_1732])).
% 9.16/3.33  tff(c_13235, plain, (![B_363]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_363))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_363)) | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_13217])).
% 9.16/3.33  tff(c_13467, plain, (![B_368]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_368))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_368)) | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_13235])).
% 9.16/3.33  tff(c_13493, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_13467])).
% 9.16/3.33  tff(c_13503, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_2619, c_13493])).
% 9.16/3.33  tff(c_13505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2046, c_13503])).
% 9.16/3.33  tff(c_13506, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 9.16/3.33  tff(c_13813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13506, c_138])).
% 9.16/3.33  tff(c_13814, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 9.16/3.33  tff(c_13913, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13814, c_58])).
% 9.16/3.33  tff(c_14657, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14656, c_13913])).
% 9.16/3.33  tff(c_14798, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14772, c_14657])).
% 9.16/3.33  tff(c_14920, plain, (![A_454, B_455]: (k2_pre_topc(A_454, B_455)=B_455 | ~v4_pre_topc(B_455, A_454) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.16/3.33  tff(c_14939, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_14920])).
% 9.16/3.33  tff(c_14946, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_13814, c_14939])).
% 9.16/3.33  tff(c_17148, plain, (![A_519, B_520]: (k7_subset_1(u1_struct_0(A_519), k2_pre_topc(A_519, B_520), k1_tops_1(A_519, B_520))=k2_tops_1(A_519, B_520) | ~m1_subset_1(B_520, k1_zfmisc_1(u1_struct_0(A_519))) | ~l1_pre_topc(A_519))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.16/3.33  tff(c_17157, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14946, c_17148])).
% 9.16/3.33  tff(c_17161, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_14772, c_14656, c_17157])).
% 9.16/3.33  tff(c_17163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14798, c_17161])).
% 9.16/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.16/3.33  
% 9.16/3.33  Inference rules
% 9.16/3.33  ----------------------
% 9.16/3.33  #Ref     : 2
% 9.16/3.33  #Sup     : 4175
% 9.16/3.33  #Fact    : 0
% 9.16/3.33  #Define  : 0
% 9.16/3.33  #Split   : 9
% 9.16/3.33  #Chain   : 0
% 9.16/3.33  #Close   : 0
% 9.16/3.33  
% 9.16/3.33  Ordering : KBO
% 9.16/3.33  
% 9.16/3.33  Simplification rules
% 9.16/3.33  ----------------------
% 9.16/3.33  #Subsume      : 355
% 9.16/3.33  #Demod        : 5065
% 9.16/3.33  #Tautology    : 2945
% 9.16/3.33  #SimpNegUnit  : 109
% 9.16/3.33  #BackRed      : 10
% 9.16/3.33  
% 9.16/3.33  #Partial instantiations: 0
% 9.16/3.33  #Strategies tried      : 1
% 9.16/3.33  
% 9.16/3.33  Timing (in seconds)
% 9.16/3.33  ----------------------
% 9.16/3.34  Preprocessing        : 0.33
% 9.16/3.34  Parsing              : 0.18
% 9.16/3.34  CNF conversion       : 0.02
% 9.16/3.34  Main loop            : 2.22
% 9.16/3.34  Inferencing          : 0.54
% 9.16/3.34  Reduction            : 1.14
% 9.16/3.34  Demodulation         : 0.95
% 9.16/3.34  BG Simplification    : 0.05
% 9.16/3.34  Subsumption          : 0.36
% 9.16/3.34  Abstraction          : 0.10
% 9.16/3.34  MUC search           : 0.00
% 9.16/3.34  Cooper               : 0.00
% 9.16/3.34  Total                : 2.60
% 9.16/3.34  Index Insertion      : 0.00
% 9.16/3.34  Index Deletion       : 0.00
% 9.16/3.34  Index Matching       : 0.00
% 9.16/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
