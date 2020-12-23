%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 157 expanded)
%              Number of leaves         :   36 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 304 expanded)
%              Number of equality atoms :   54 (  91 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1190,plain,(
    ! [A_164,B_165,C_166] :
      ( k7_subset_1(A_164,B_165,C_166) = k4_xboole_0(B_165,C_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1198,plain,(
    ! [C_166] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_166) = k4_xboole_0('#skF_2',C_166) ),
    inference(resolution,[status(thm)],[c_36,c_1190])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_85,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_357,plain,(
    ! [B_89,A_90] :
      ( v4_pre_topc(B_89,A_90)
      | k2_pre_topc(A_90,B_89) != B_89
      | ~ v2_pre_topc(A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_367,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_357])).

tff(c_376,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_367])).

tff(c_377,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_376])).

tff(c_106,plain,(
    ! [A_51,B_52,C_53] :
      ( k7_subset_1(A_51,B_52,C_53) = k4_xboole_0(B_52,C_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [C_57] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_57) = k4_xboole_0('#skF_2',C_57) ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_138,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_48])).

tff(c_149,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_138])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k4_subset_1(A_18,B_19,k2_subset_1(A_18)) = k2_subset_1(A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [A_49,B_50] :
      ( k4_subset_1(A_49,B_50,A_49) = A_49
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_18])).

tff(c_158,plain,(
    ! [B_58,A_59] :
      ( k4_subset_1(B_58,A_59,B_58) = B_58
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_169,plain,(
    ! [A_1,B_2] : k4_subset_1(A_1,k4_xboole_0(A_1,B_2),A_1) = A_1 ),
    inference(resolution,[status(thm)],[c_2,c_158])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_471,plain,(
    ! [A_97,C_98,B_99] :
      ( k4_subset_1(A_97,C_98,B_99) = k4_subset_1(A_97,B_99,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_484,plain,(
    ! [A_100,B_101] :
      ( k4_subset_1(A_100,B_101,A_100) = k4_subset_1(A_100,A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(resolution,[status(thm)],[c_49,c_471])).

tff(c_532,plain,(
    ! [B_103,A_104] :
      ( k4_subset_1(B_103,B_103,A_104) = k4_subset_1(B_103,A_104,B_103)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_22,c_484])).

tff(c_542,plain,(
    ! [A_1,B_2] : k4_subset_1(A_1,k4_xboole_0(A_1,B_2),A_1) = k4_subset_1(A_1,A_1,k4_xboole_0(A_1,B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_532])).

tff(c_551,plain,(
    ! [A_1,B_2] : k4_subset_1(A_1,A_1,k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_542])).

tff(c_316,plain,(
    ! [A_83,B_84,C_85] :
      ( k4_subset_1(A_83,B_84,C_85) = k2_xboole_0(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_569,plain,(
    ! [B_107,B_108,A_109] :
      ( k4_subset_1(B_107,B_108,A_109) = k2_xboole_0(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(B_107))
      | ~ r1_tarski(A_109,B_107) ) ),
    inference(resolution,[status(thm)],[c_22,c_316])).

tff(c_603,plain,(
    ! [A_112,A_113] :
      ( k4_subset_1(A_112,A_112,A_113) = k2_xboole_0(A_112,A_113)
      | ~ r1_tarski(A_113,A_112) ) ),
    inference(resolution,[status(thm)],[c_49,c_569])).

tff(c_613,plain,(
    ! [A_1,B_2] : k4_subset_1(A_1,A_1,k4_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_603])).

tff(c_623,plain,(
    ! [A_114,B_115] : k2_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_613])).

tff(c_632,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_623])).

tff(c_582,plain,(
    ! [A_110,B_111] :
      ( k4_subset_1(u1_struct_0(A_110),B_111,k2_tops_1(A_110,B_111)) = k2_pre_topc(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_589,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_582])).

tff(c_597,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_589])).

tff(c_287,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k2_tops_1(A_79,B_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_304,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k2_tops_1(A_79,B_80),u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_287,c_20])).

tff(c_635,plain,(
    ! [A_116] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_116) = k2_xboole_0('#skF_2',A_116)
      | ~ r1_tarski(A_116,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_36,c_569])).

tff(c_639,plain,(
    ! [B_80] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_80)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_80))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_304,c_635])).

tff(c_1108,plain,(
    ! [B_153] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_153)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_639])).

tff(c_1119,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_1108])).

tff(c_1129,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_597,c_1119])).

tff(c_1131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_1129])).

tff(c_1132,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1209,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1132])).

tff(c_1133,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1277,plain,(
    ! [A_185,B_186] :
      ( k2_pre_topc(A_185,B_186) = B_186
      | ~ v4_pre_topc(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1287,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1277])).

tff(c_1296,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1133,c_1287])).

tff(c_1938,plain,(
    ! [A_251,B_252] :
      ( k7_subset_1(u1_struct_0(A_251),k2_pre_topc(A_251,B_252),k1_tops_1(A_251,B_252)) = k2_tops_1(A_251,B_252)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1947,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_1938])).

tff(c_1951,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1198,c_1947])).

tff(c_1953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1209,c_1951])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.78  
% 3.99/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.79  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.99/1.79  
% 3.99/1.79  %Foreground sorts:
% 3.99/1.79  
% 3.99/1.79  
% 3.99/1.79  %Background operators:
% 3.99/1.79  
% 3.99/1.79  
% 3.99/1.79  %Foreground operators:
% 3.99/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.99/1.79  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.99/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.99/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.99/1.79  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.99/1.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.99/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.99/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.99/1.79  tff('#skF_1', type, '#skF_1': $i).
% 3.99/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.79  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.99/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.99/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.99/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.99/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.99/1.79  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.99/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.79  
% 3.99/1.80  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.99/1.80  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.99/1.80  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.99/1.80  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.99/1.80  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.99/1.80  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.99/1.80  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.99/1.80  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.99/1.80  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 3.99/1.80  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.99/1.80  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.99/1.80  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.99/1.80  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.99/1.80  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.99/1.80  tff(c_1190, plain, (![A_164, B_165, C_166]: (k7_subset_1(A_164, B_165, C_166)=k4_xboole_0(B_165, C_166) | ~m1_subset_1(B_165, k1_zfmisc_1(A_164)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.99/1.80  tff(c_1198, plain, (![C_166]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_166)=k4_xboole_0('#skF_2', C_166))), inference(resolution, [status(thm)], [c_36, c_1190])).
% 3.99/1.80  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.99/1.80  tff(c_85, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 3.99/1.80  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.99/1.80  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.99/1.80  tff(c_357, plain, (![B_89, A_90]: (v4_pre_topc(B_89, A_90) | k2_pre_topc(A_90, B_89)!=B_89 | ~v2_pre_topc(A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.99/1.80  tff(c_367, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_357])).
% 3.99/1.80  tff(c_376, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_367])).
% 3.99/1.80  tff(c_377, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_85, c_376])).
% 3.99/1.80  tff(c_106, plain, (![A_51, B_52, C_53]: (k7_subset_1(A_51, B_52, C_53)=k4_xboole_0(B_52, C_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.99/1.80  tff(c_143, plain, (![C_57]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_57)=k4_xboole_0('#skF_2', C_57))), inference(resolution, [status(thm)], [c_36, c_106])).
% 3.99/1.80  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.99/1.80  tff(c_138, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_85, c_48])).
% 3.99/1.80  tff(c_149, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_138])).
% 3.99/1.80  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.80  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.99/1.80  tff(c_10, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.99/1.80  tff(c_18, plain, (![A_18, B_19]: (k4_subset_1(A_18, B_19, k2_subset_1(A_18))=k2_subset_1(A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.80  tff(c_96, plain, (![A_49, B_50]: (k4_subset_1(A_49, B_50, A_49)=A_49 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_18])).
% 3.99/1.80  tff(c_158, plain, (![B_58, A_59]: (k4_subset_1(B_58, A_59, B_58)=B_58 | ~r1_tarski(A_59, B_58))), inference(resolution, [status(thm)], [c_22, c_96])).
% 3.99/1.80  tff(c_169, plain, (![A_1, B_2]: (k4_subset_1(A_1, k4_xboole_0(A_1, B_2), A_1)=A_1)), inference(resolution, [status(thm)], [c_2, c_158])).
% 3.99/1.80  tff(c_12, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.80  tff(c_49, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.99/1.80  tff(c_471, plain, (![A_97, C_98, B_99]: (k4_subset_1(A_97, C_98, B_99)=k4_subset_1(A_97, B_99, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.80  tff(c_484, plain, (![A_100, B_101]: (k4_subset_1(A_100, B_101, A_100)=k4_subset_1(A_100, A_100, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(resolution, [status(thm)], [c_49, c_471])).
% 3.99/1.80  tff(c_532, plain, (![B_103, A_104]: (k4_subset_1(B_103, B_103, A_104)=k4_subset_1(B_103, A_104, B_103) | ~r1_tarski(A_104, B_103))), inference(resolution, [status(thm)], [c_22, c_484])).
% 3.99/1.80  tff(c_542, plain, (![A_1, B_2]: (k4_subset_1(A_1, k4_xboole_0(A_1, B_2), A_1)=k4_subset_1(A_1, A_1, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_532])).
% 3.99/1.80  tff(c_551, plain, (![A_1, B_2]: (k4_subset_1(A_1, A_1, k4_xboole_0(A_1, B_2))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_542])).
% 3.99/1.80  tff(c_316, plain, (![A_83, B_84, C_85]: (k4_subset_1(A_83, B_84, C_85)=k2_xboole_0(B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.99/1.80  tff(c_569, plain, (![B_107, B_108, A_109]: (k4_subset_1(B_107, B_108, A_109)=k2_xboole_0(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(B_107)) | ~r1_tarski(A_109, B_107))), inference(resolution, [status(thm)], [c_22, c_316])).
% 3.99/1.80  tff(c_603, plain, (![A_112, A_113]: (k4_subset_1(A_112, A_112, A_113)=k2_xboole_0(A_112, A_113) | ~r1_tarski(A_113, A_112))), inference(resolution, [status(thm)], [c_49, c_569])).
% 3.99/1.80  tff(c_613, plain, (![A_1, B_2]: (k4_subset_1(A_1, A_1, k4_xboole_0(A_1, B_2))=k2_xboole_0(A_1, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_603])).
% 3.99/1.80  tff(c_623, plain, (![A_114, B_115]: (k2_xboole_0(A_114, k4_xboole_0(A_114, B_115))=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_551, c_613])).
% 3.99/1.80  tff(c_632, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_149, c_623])).
% 3.99/1.80  tff(c_582, plain, (![A_110, B_111]: (k4_subset_1(u1_struct_0(A_110), B_111, k2_tops_1(A_110, B_111))=k2_pre_topc(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.99/1.80  tff(c_589, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_582])).
% 3.99/1.80  tff(c_597, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_589])).
% 3.99/1.80  tff(c_287, plain, (![A_79, B_80]: (m1_subset_1(k2_tops_1(A_79, B_80), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.99/1.80  tff(c_20, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.99/1.80  tff(c_304, plain, (![A_79, B_80]: (r1_tarski(k2_tops_1(A_79, B_80), u1_struct_0(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_287, c_20])).
% 3.99/1.80  tff(c_635, plain, (![A_116]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_116)=k2_xboole_0('#skF_2', A_116) | ~r1_tarski(A_116, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_569])).
% 3.99/1.80  tff(c_639, plain, (![B_80]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_80))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_80)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_304, c_635])).
% 3.99/1.80  tff(c_1108, plain, (![B_153]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_153))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_639])).
% 3.99/1.80  tff(c_1119, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_1108])).
% 3.99/1.80  tff(c_1129, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_632, c_597, c_1119])).
% 3.99/1.80  tff(c_1131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_377, c_1129])).
% 3.99/1.80  tff(c_1132, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.99/1.80  tff(c_1209, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1132])).
% 3.99/1.80  tff(c_1133, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.99/1.80  tff(c_1277, plain, (![A_185, B_186]: (k2_pre_topc(A_185, B_186)=B_186 | ~v4_pre_topc(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.99/1.80  tff(c_1287, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1277])).
% 3.99/1.80  tff(c_1296, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1133, c_1287])).
% 3.99/1.80  tff(c_1938, plain, (![A_251, B_252]: (k7_subset_1(u1_struct_0(A_251), k2_pre_topc(A_251, B_252), k1_tops_1(A_251, B_252))=k2_tops_1(A_251, B_252) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.99/1.80  tff(c_1947, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1296, c_1938])).
% 3.99/1.80  tff(c_1951, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1198, c_1947])).
% 3.99/1.80  tff(c_1953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1209, c_1951])).
% 3.99/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.80  
% 3.99/1.80  Inference rules
% 3.99/1.80  ----------------------
% 3.99/1.80  #Ref     : 0
% 3.99/1.80  #Sup     : 439
% 3.99/1.80  #Fact    : 0
% 3.99/1.80  #Define  : 0
% 3.99/1.80  #Split   : 1
% 3.99/1.80  #Chain   : 0
% 3.99/1.80  #Close   : 0
% 3.99/1.80  
% 3.99/1.80  Ordering : KBO
% 3.99/1.80  
% 3.99/1.80  Simplification rules
% 3.99/1.80  ----------------------
% 3.99/1.80  #Subsume      : 25
% 3.99/1.80  #Demod        : 245
% 3.99/1.80  #Tautology    : 223
% 3.99/1.80  #SimpNegUnit  : 6
% 3.99/1.80  #BackRed      : 6
% 3.99/1.80  
% 3.99/1.80  #Partial instantiations: 0
% 3.99/1.80  #Strategies tried      : 1
% 3.99/1.80  
% 3.99/1.80  Timing (in seconds)
% 3.99/1.80  ----------------------
% 3.99/1.81  Preprocessing        : 0.36
% 3.99/1.81  Parsing              : 0.20
% 3.99/1.81  CNF conversion       : 0.02
% 3.99/1.81  Main loop            : 0.59
% 3.99/1.81  Inferencing          : 0.22
% 3.99/1.81  Reduction            : 0.19
% 3.99/1.81  Demodulation         : 0.14
% 3.99/1.81  BG Simplification    : 0.03
% 3.99/1.81  Subsumption          : 0.10
% 3.99/1.81  Abstraction          : 0.04
% 3.99/1.81  MUC search           : 0.00
% 3.99/1.81  Cooper               : 0.00
% 3.99/1.81  Total                : 0.99
% 3.99/1.81  Index Insertion      : 0.00
% 3.99/1.81  Index Deletion       : 0.00
% 3.99/1.81  Index Matching       : 0.00
% 3.99/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
