%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:53 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 157 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  170 ( 497 expanded)
%              Number of equality atoms :   36 (  82 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_329,plain,(
    ! [B_82,A_83] :
      ( v2_tops_1(B_82,A_83)
      | k1_tops_1(A_83,B_82) != k1_xboole_0
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_336,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_329])).

tff(c_340,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_336])).

tff(c_341,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_340])).

tff(c_65,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_153,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_tops_1(A_67,B_68),B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_162,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_158])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_455,plain,(
    ! [A_90,B_91] :
      ( v3_pre_topc(k1_tops_1(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_460,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_455])).

tff(c_464,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_460])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_56,B_2,A_1] :
      ( r1_tarski(A_56,B_2)
      | ~ r1_tarski(A_56,A_1)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_173,plain,(
    ! [B_2] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_2)
      | k4_xboole_0('#skF_2',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_162,c_92])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [C_46] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_46
      | ~ v3_pre_topc(C_46,'#skF_1')
      | ~ r1_tarski(C_46,'#skF_2')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_187,plain,(
    ! [C_70] :
      ( k1_xboole_0 = C_70
      | ~ v3_pre_topc(C_70,'#skF_1')
      | ~ r1_tarski(C_70,'#skF_2')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52])).

tff(c_621,plain,(
    ! [A_106] :
      ( k1_xboole_0 = A_106
      | ~ v3_pre_topc(A_106,'#skF_1')
      | ~ r1_tarski(A_106,'#skF_2')
      | ~ r1_tarski(A_106,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_187])).

tff(c_636,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_621])).

tff(c_652,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_162,c_464,c_636])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_652])).

tff(c_655,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_656,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_658,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_38])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_660,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_36])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_681,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_40])).

tff(c_22,plain,(
    ! [B_29,D_35,C_33,A_21] :
      ( k1_tops_1(B_29,D_35) = D_35
      | ~ v3_pre_topc(D_35,B_29)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2393,plain,(
    ! [C_199,A_200] :
      ( ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200) ) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_2400,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_681,c_2393])).

tff(c_2408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2400])).

tff(c_2908,plain,(
    ! [B_213,D_214] :
      ( k1_tops_1(B_213,D_214) = D_214
      | ~ v3_pre_topc(D_214,B_213)
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0(B_213)))
      | ~ l1_pre_topc(B_213) ) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_2915,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_681,c_2908])).

tff(c_2922,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_660,c_2915])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1453,plain,(
    ! [A_161,B_162] :
      ( k1_tops_1(A_161,B_162) = k1_xboole_0
      | ~ v2_tops_1(B_162,A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1463,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1453])).

tff(c_1470,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_656,c_1463])).

tff(c_1661,plain,(
    ! [A_173,B_174,C_175] :
      ( r1_tarski(k1_tops_1(A_173,B_174),k1_tops_1(A_173,C_175))
      | ~ r1_tarski(B_174,C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4911,plain,(
    ! [A_287,B_288,C_289] :
      ( k4_xboole_0(k1_tops_1(A_287,B_288),k1_tops_1(A_287,C_289)) = k1_xboole_0
      | ~ r1_tarski(B_288,C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_pre_topc(A_287) ) ),
    inference(resolution,[status(thm)],[c_1661,c_4])).

tff(c_4918,plain,(
    ! [B_288] :
      ( k4_xboole_0(k1_tops_1('#skF_1',B_288),k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0
      | ~ r1_tarski(B_288,'#skF_2')
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_4911])).

tff(c_4949,plain,(
    ! [B_291] :
      ( k1_tops_1('#skF_1',B_291) = k1_xboole_0
      | ~ r1_tarski(B_291,'#skF_2')
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8,c_1470,c_4918])).

tff(c_4956,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_681,c_4949])).

tff(c_4963,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_2922,c_4956])).

tff(c_4965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_4963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/2.10  
% 5.38/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/2.10  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.38/2.10  
% 5.38/2.10  %Foreground sorts:
% 5.38/2.10  
% 5.38/2.10  
% 5.38/2.10  %Background operators:
% 5.38/2.10  
% 5.38/2.10  
% 5.38/2.10  %Foreground operators:
% 5.38/2.10  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.38/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.38/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.38/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.38/2.10  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.38/2.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.38/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.38/2.10  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.38/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.38/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.38/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.38/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.38/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.38/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.38/2.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.38/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.38/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.38/2.10  
% 5.73/2.12  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 5.73/2.12  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 5.73/2.12  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.73/2.12  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.73/2.12  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.73/2.12  tff(f_49, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.73/2.12  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.73/2.12  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 5.73/2.12  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.73/2.12  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 5.73/2.12  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_62, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 5.73/2.12  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_329, plain, (![B_82, A_83]: (v2_tops_1(B_82, A_83) | k1_tops_1(A_83, B_82)!=k1_xboole_0 | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.73/2.12  tff(c_336, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_329])).
% 5.73/2.12  tff(c_340, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_336])).
% 5.73/2.12  tff(c_341, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_340])).
% 5.73/2.12  tff(c_65, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.73/2.12  tff(c_73, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_65])).
% 5.73/2.12  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.12  tff(c_77, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_4])).
% 5.73/2.12  tff(c_153, plain, (![A_67, B_68]: (r1_tarski(k1_tops_1(A_67, B_68), B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.73/2.12  tff(c_158, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_153])).
% 5.73/2.12  tff(c_162, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_158])).
% 5.73/2.12  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_455, plain, (![A_90, B_91]: (v3_pre_topc(k1_tops_1(A_90, B_91), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.73/2.12  tff(c_460, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_455])).
% 5.73/2.12  tff(c_464, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_460])).
% 5.73/2.12  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.12  tff(c_87, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.73/2.12  tff(c_92, plain, (![A_56, B_2, A_1]: (r1_tarski(A_56, B_2) | ~r1_tarski(A_56, A_1) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 5.73/2.12  tff(c_173, plain, (![B_2]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_2) | k4_xboole_0('#skF_2', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_162, c_92])).
% 5.73/2.12  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.73/2.12  tff(c_52, plain, (![C_46]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_46 | ~v3_pre_topc(C_46, '#skF_1') | ~r1_tarski(C_46, '#skF_2') | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_187, plain, (![C_70]: (k1_xboole_0=C_70 | ~v3_pre_topc(C_70, '#skF_1') | ~r1_tarski(C_70, '#skF_2') | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_52])).
% 5.73/2.12  tff(c_621, plain, (![A_106]: (k1_xboole_0=A_106 | ~v3_pre_topc(A_106, '#skF_1') | ~r1_tarski(A_106, '#skF_2') | ~r1_tarski(A_106, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_187])).
% 5.73/2.12  tff(c_636, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_173, c_621])).
% 5.73/2.12  tff(c_652, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_162, c_464, c_636])).
% 5.73/2.12  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_341, c_652])).
% 5.73/2.12  tff(c_655, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 5.73/2.12  tff(c_656, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 5.73/2.12  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_658, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_38])).
% 5.73/2.12  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_660, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_36])).
% 5.73/2.12  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.73/2.12  tff(c_681, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_40])).
% 5.73/2.12  tff(c_22, plain, (![B_29, D_35, C_33, A_21]: (k1_tops_1(B_29, D_35)=D_35 | ~v3_pre_topc(D_35, B_29) | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(B_29))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.73/2.12  tff(c_2393, plain, (![C_199, A_200]: (~m1_subset_1(C_199, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200))), inference(splitLeft, [status(thm)], [c_22])).
% 5.73/2.12  tff(c_2400, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_681, c_2393])).
% 5.73/2.12  tff(c_2408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2400])).
% 5.73/2.12  tff(c_2908, plain, (![B_213, D_214]: (k1_tops_1(B_213, D_214)=D_214 | ~v3_pre_topc(D_214, B_213) | ~m1_subset_1(D_214, k1_zfmisc_1(u1_struct_0(B_213))) | ~l1_pre_topc(B_213))), inference(splitRight, [status(thm)], [c_22])).
% 5.73/2.12  tff(c_2915, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_681, c_2908])).
% 5.73/2.12  tff(c_2922, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_660, c_2915])).
% 5.73/2.12  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.73/2.12  tff(c_1453, plain, (![A_161, B_162]: (k1_tops_1(A_161, B_162)=k1_xboole_0 | ~v2_tops_1(B_162, A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.73/2.12  tff(c_1463, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1453])).
% 5.73/2.12  tff(c_1470, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_656, c_1463])).
% 5.73/2.12  tff(c_1661, plain, (![A_173, B_174, C_175]: (r1_tarski(k1_tops_1(A_173, B_174), k1_tops_1(A_173, C_175)) | ~r1_tarski(B_174, C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.73/2.12  tff(c_4911, plain, (![A_287, B_288, C_289]: (k4_xboole_0(k1_tops_1(A_287, B_288), k1_tops_1(A_287, C_289))=k1_xboole_0 | ~r1_tarski(B_288, C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(u1_struct_0(A_287))) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0(A_287))) | ~l1_pre_topc(A_287))), inference(resolution, [status(thm)], [c_1661, c_4])).
% 5.73/2.12  tff(c_4918, plain, (![B_288]: (k4_xboole_0(k1_tops_1('#skF_1', B_288), k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0 | ~r1_tarski(B_288, '#skF_2') | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_4911])).
% 5.73/2.12  tff(c_4949, plain, (![B_291]: (k1_tops_1('#skF_1', B_291)=k1_xboole_0 | ~r1_tarski(B_291, '#skF_2') | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8, c_1470, c_4918])).
% 5.73/2.12  tff(c_4956, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_681, c_4949])).
% 5.73/2.12  tff(c_4963, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_2922, c_4956])).
% 5.73/2.12  tff(c_4965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_655, c_4963])).
% 5.73/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.12  
% 5.73/2.12  Inference rules
% 5.73/2.12  ----------------------
% 5.73/2.12  #Ref     : 0
% 5.73/2.12  #Sup     : 1126
% 5.73/2.12  #Fact    : 0
% 5.73/2.12  #Define  : 0
% 5.73/2.12  #Split   : 22
% 5.73/2.12  #Chain   : 0
% 5.73/2.12  #Close   : 0
% 5.73/2.12  
% 5.73/2.12  Ordering : KBO
% 5.73/2.12  
% 5.73/2.12  Simplification rules
% 5.73/2.12  ----------------------
% 5.73/2.12  #Subsume      : 503
% 5.73/2.12  #Demod        : 584
% 5.73/2.12  #Tautology    : 342
% 5.73/2.12  #SimpNegUnit  : 33
% 5.73/2.12  #BackRed      : 35
% 5.73/2.12  
% 5.73/2.12  #Partial instantiations: 0
% 5.73/2.12  #Strategies tried      : 1
% 5.73/2.12  
% 5.73/2.12  Timing (in seconds)
% 5.73/2.12  ----------------------
% 5.73/2.12  Preprocessing        : 0.34
% 5.73/2.12  Parsing              : 0.18
% 5.73/2.12  CNF conversion       : 0.03
% 5.73/2.12  Main loop            : 0.95
% 5.73/2.12  Inferencing          : 0.29
% 5.73/2.12  Reduction            : 0.31
% 5.73/2.12  Demodulation         : 0.20
% 5.73/2.12  BG Simplification    : 0.03
% 5.73/2.12  Subsumption          : 0.25
% 5.73/2.12  Abstraction          : 0.04
% 5.73/2.12  MUC search           : 0.00
% 5.73/2.12  Cooper               : 0.00
% 5.73/2.12  Total                : 1.33
% 5.73/2.12  Index Insertion      : 0.00
% 5.73/2.12  Index Deletion       : 0.00
% 5.73/2.12  Index Matching       : 0.00
% 5.73/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
