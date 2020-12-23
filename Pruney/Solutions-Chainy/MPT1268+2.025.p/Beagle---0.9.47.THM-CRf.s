%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 181 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 556 expanded)
%              Number of equality atoms :   28 (  81 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_68,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_76,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_77,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    k4_xboole_0('#skF_3',u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_77])).

tff(c_364,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_tops_1(A_98,B_99),B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_369,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_364])).

tff(c_373,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_369])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_500,plain,(
    ! [A_102,B_103] :
      ( v3_pre_topc(k1_tops_1(A_102,B_103),A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_505,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_500])).

tff(c_509,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_505])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_158,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_166,plain,(
    ! [A_67,B_9,A_8] :
      ( r1_tarski(A_67,B_9)
      | ~ r1_tarski(A_67,A_8)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_391,plain,(
    ! [B_9] :
      ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),B_9)
      | k4_xboole_0('#skF_3',B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_373,c_166])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    ! [C_43] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_43
      | ~ v3_pre_topc(C_43,'#skF_2')
      | ~ r1_tarski(C_43,'#skF_3')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_144,plain,(
    ! [C_66] :
      ( k1_xboole_0 = C_66
      | ~ v3_pre_topc(C_66,'#skF_2')
      | ~ r1_tarski(C_66,'#skF_3')
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_62])).

tff(c_517,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | ~ v3_pre_topc(A_105,'#skF_2')
      | ~ r1_tarski(A_105,'#skF_3')
      | ~ r1_tarski(A_105,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_26,c_144])).

tff(c_521,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | k4_xboole_0('#skF_3',u1_struct_0('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_517])).

tff(c_541,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_373,c_509,c_521])).

tff(c_602,plain,(
    ! [B_106,A_107] :
      ( v2_tops_1(B_106,A_107)
      | k1_tops_1(A_107,B_106) != k1_xboole_0
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_609,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_602])).

tff(c_613,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_541,c_609])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_613])).

tff(c_616,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_617,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_619,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_46])).

tff(c_48,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_621,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_48])).

tff(c_50,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_666,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_50])).

tff(c_1317,plain,(
    ! [A_168,B_169] :
      ( k1_tops_1(A_168,B_169) = k1_xboole_0
      | ~ v2_tops_1(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1327,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1317])).

tff(c_1335,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_617,c_1327])).

tff(c_1386,plain,(
    ! [B_170,A_171,C_172] :
      ( r1_tarski(B_170,k1_tops_1(A_171,C_172))
      | ~ r1_tarski(B_170,C_172)
      | ~ v3_pre_topc(B_170,A_171)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1393,plain,(
    ! [B_170] :
      ( r1_tarski(B_170,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_170,'#skF_3')
      | ~ v3_pre_topc(B_170,'#skF_2')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_1386])).

tff(c_1413,plain,(
    ! [B_174] :
      ( r1_tarski(B_174,k1_xboole_0)
      | ~ r1_tarski(B_174,'#skF_3')
      | ~ v3_pre_topc(B_174,'#skF_2')
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1335,c_1393])).

tff(c_1416,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_666,c_1413])).

tff(c_1426,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_621,c_1416])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_624,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k1_xboole_0
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_636,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_624])).

tff(c_703,plain,(
    ! [A_119,C_120,B_121] :
      ( r1_xboole_0(A_119,k4_xboole_0(C_120,B_121))
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_716,plain,(
    ! [A_122,B_123] :
      ( r1_xboole_0(A_122,k1_xboole_0)
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_703])).

tff(c_731,plain,(
    ! [B_7] : r1_xboole_0(B_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_716])).

tff(c_831,plain,(
    ! [A_142,B_143,C_144] :
      ( k1_xboole_0 = A_142
      | ~ r1_xboole_0(B_143,C_144)
      | ~ r1_tarski(A_142,C_144)
      | ~ r1_tarski(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_839,plain,(
    ! [A_142,B_7] :
      ( k1_xboole_0 = A_142
      | ~ r1_tarski(A_142,k1_xboole_0)
      | ~ r1_tarski(A_142,B_7) ) ),
    inference(resolution,[status(thm)],[c_731,c_831])).

tff(c_1441,plain,(
    ! [B_7] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r1_tarski('#skF_4',B_7) ) ),
    inference(resolution,[status(thm)],[c_1426,c_839])).

tff(c_1458,plain,(
    ! [B_7] : ~ r1_tarski('#skF_4',B_7) ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_1441])).

tff(c_1471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1458,c_1426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.55  
% 3.32/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.56  
% 3.32/1.56  %Foreground sorts:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Background operators:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Foreground operators:
% 3.32/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.32/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.32/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.56  
% 3.32/1.57  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.32/1.57  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.57  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.32/1.57  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.32/1.57  tff(f_83, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.32/1.57  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.32/1.57  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.32/1.57  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.32/1.57  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.57  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.32/1.57  tff(f_67, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.32/1.57  tff(c_44, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_65, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 3.32/1.57  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_68, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.57  tff(c_76, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_68])).
% 3.32/1.57  tff(c_77, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.57  tff(c_87, plain, (k4_xboole_0('#skF_3', u1_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_77])).
% 3.32/1.57  tff(c_364, plain, (![A_98, B_99]: (r1_tarski(k1_tops_1(A_98, B_99), B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.57  tff(c_369, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_364])).
% 3.32/1.57  tff(c_373, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_369])).
% 3.32/1.57  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_500, plain, (![A_102, B_103]: (v3_pre_topc(k1_tops_1(A_102, B_103), A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.57  tff(c_505, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_500])).
% 3.32/1.57  tff(c_509, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_505])).
% 3.32/1.57  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.57  tff(c_158, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.57  tff(c_166, plain, (![A_67, B_9, A_8]: (r1_tarski(A_67, B_9) | ~r1_tarski(A_67, A_8) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_158])).
% 3.32/1.57  tff(c_391, plain, (![B_9]: (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), B_9) | k4_xboole_0('#skF_3', B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_373, c_166])).
% 3.32/1.57  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.57  tff(c_62, plain, (![C_43]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_43 | ~v3_pre_topc(C_43, '#skF_2') | ~r1_tarski(C_43, '#skF_3') | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_144, plain, (![C_66]: (k1_xboole_0=C_66 | ~v3_pre_topc(C_66, '#skF_2') | ~r1_tarski(C_66, '#skF_3') | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_65, c_62])).
% 3.32/1.57  tff(c_517, plain, (![A_105]: (k1_xboole_0=A_105 | ~v3_pre_topc(A_105, '#skF_2') | ~r1_tarski(A_105, '#skF_3') | ~r1_tarski(A_105, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_26, c_144])).
% 3.32/1.57  tff(c_521, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | k4_xboole_0('#skF_3', u1_struct_0('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_391, c_517])).
% 3.32/1.57  tff(c_541, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_87, c_373, c_509, c_521])).
% 3.32/1.57  tff(c_602, plain, (![B_106, A_107]: (v2_tops_1(B_106, A_107) | k1_tops_1(A_107, B_106)!=k1_xboole_0 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.57  tff(c_609, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_602])).
% 3.32/1.57  tff(c_613, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_541, c_609])).
% 3.32/1.57  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_613])).
% 3.32/1.57  tff(c_616, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 3.32/1.57  tff(c_617, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.32/1.57  tff(c_46, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_619, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_46])).
% 3.32/1.57  tff(c_48, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_621, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_48])).
% 3.32/1.57  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.57  tff(c_666, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_617, c_50])).
% 3.32/1.57  tff(c_1317, plain, (![A_168, B_169]: (k1_tops_1(A_168, B_169)=k1_xboole_0 | ~v2_tops_1(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.57  tff(c_1327, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1317])).
% 3.32/1.57  tff(c_1335, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_617, c_1327])).
% 3.32/1.57  tff(c_1386, plain, (![B_170, A_171, C_172]: (r1_tarski(B_170, k1_tops_1(A_171, C_172)) | ~r1_tarski(B_170, C_172) | ~v3_pre_topc(B_170, A_171) | ~m1_subset_1(C_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.32/1.57  tff(c_1393, plain, (![B_170]: (r1_tarski(B_170, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_170, '#skF_3') | ~v3_pre_topc(B_170, '#skF_2') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_1386])).
% 3.32/1.57  tff(c_1413, plain, (![B_174]: (r1_tarski(B_174, k1_xboole_0) | ~r1_tarski(B_174, '#skF_3') | ~v3_pre_topc(B_174, '#skF_2') | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1335, c_1393])).
% 3.32/1.57  tff(c_1416, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_666, c_1413])).
% 3.32/1.57  tff(c_1426, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_619, c_621, c_1416])).
% 3.32/1.57  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.57  tff(c_624, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k1_xboole_0 | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.57  tff(c_636, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_624])).
% 3.32/1.57  tff(c_703, plain, (![A_119, C_120, B_121]: (r1_xboole_0(A_119, k4_xboole_0(C_120, B_121)) | ~r1_tarski(A_119, B_121))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.32/1.57  tff(c_716, plain, (![A_122, B_123]: (r1_xboole_0(A_122, k1_xboole_0) | ~r1_tarski(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_636, c_703])).
% 3.32/1.57  tff(c_731, plain, (![B_7]: (r1_xboole_0(B_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_716])).
% 3.32/1.57  tff(c_831, plain, (![A_142, B_143, C_144]: (k1_xboole_0=A_142 | ~r1_xboole_0(B_143, C_144) | ~r1_tarski(A_142, C_144) | ~r1_tarski(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.57  tff(c_839, plain, (![A_142, B_7]: (k1_xboole_0=A_142 | ~r1_tarski(A_142, k1_xboole_0) | ~r1_tarski(A_142, B_7))), inference(resolution, [status(thm)], [c_731, c_831])).
% 3.32/1.57  tff(c_1441, plain, (![B_7]: (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', B_7))), inference(resolution, [status(thm)], [c_1426, c_839])).
% 3.32/1.57  tff(c_1458, plain, (![B_7]: (~r1_tarski('#skF_4', B_7))), inference(negUnitSimplification, [status(thm)], [c_616, c_1441])).
% 3.32/1.57  tff(c_1471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1458, c_1426])).
% 3.32/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  
% 3.32/1.57  Inference rules
% 3.32/1.57  ----------------------
% 3.32/1.57  #Ref     : 0
% 3.32/1.57  #Sup     : 320
% 3.32/1.57  #Fact    : 0
% 3.32/1.57  #Define  : 0
% 3.32/1.57  #Split   : 13
% 3.32/1.57  #Chain   : 0
% 3.32/1.57  #Close   : 0
% 3.32/1.57  
% 3.32/1.57  Ordering : KBO
% 3.32/1.57  
% 3.32/1.57  Simplification rules
% 3.32/1.57  ----------------------
% 3.32/1.57  #Subsume      : 65
% 3.32/1.57  #Demod        : 131
% 3.32/1.57  #Tautology    : 123
% 3.32/1.57  #SimpNegUnit  : 10
% 3.32/1.57  #BackRed      : 20
% 3.32/1.57  
% 3.32/1.57  #Partial instantiations: 0
% 3.32/1.57  #Strategies tried      : 1
% 3.32/1.57  
% 3.32/1.57  Timing (in seconds)
% 3.32/1.57  ----------------------
% 3.32/1.57  Preprocessing        : 0.32
% 3.32/1.57  Parsing              : 0.17
% 3.32/1.57  CNF conversion       : 0.02
% 3.32/1.57  Main loop            : 0.46
% 3.32/1.57  Inferencing          : 0.15
% 3.32/1.57  Reduction            : 0.14
% 3.32/1.57  Demodulation         : 0.09
% 3.32/1.58  BG Simplification    : 0.02
% 3.32/1.58  Subsumption          : 0.10
% 3.32/1.58  Abstraction          : 0.02
% 3.32/1.58  MUC search           : 0.00
% 3.32/1.58  Cooper               : 0.00
% 3.32/1.58  Total                : 0.81
% 3.32/1.58  Index Insertion      : 0.00
% 3.32/1.58  Index Deletion       : 0.00
% 3.32/1.58  Index Matching       : 0.00
% 3.32/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
