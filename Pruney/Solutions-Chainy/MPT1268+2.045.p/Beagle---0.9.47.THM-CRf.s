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
% DateTime   : Thu Dec  3 10:21:52 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 414 expanded)
%              Number of leaves         :   31 ( 151 expanded)
%              Depth                    :   15
%              Number of atoms          :  242 (1350 expanded)
%              Number of equality atoms :   41 ( 193 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_127,negated_conjecture,(
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

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_99,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_57,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_320,plain,(
    ! [B_95,A_96] :
      ( v2_tops_1(B_95,A_96)
      | k1_tops_1(A_96,B_95) != k1_xboole_0
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_327,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_320])).

tff(c_331,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_327])).

tff(c_332,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_331])).

tff(c_146,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_tops_1(A_79,B_80),B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_146])).

tff(c_155,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_151])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_268,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k1_tops_1(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_273,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_268])).

tff(c_277,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_273])).

tff(c_64,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_96,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [C_52] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_52
      | ~ v3_pre_topc(C_52,'#skF_1')
      | ~ r1_tarski(C_52,'#skF_2')
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_288,plain,(
    ! [C_92] :
      ( k1_xboole_0 = C_92
      | ~ v3_pre_topc(C_92,'#skF_1')
      | ~ r1_tarski(C_92,'#skF_2')
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_407,plain,(
    ! [A_108] :
      ( k1_xboole_0 = A_108
      | ~ v3_pre_topc(A_108,'#skF_1')
      | ~ r1_tarski(A_108,'#skF_2')
      | ~ r1_tarski(A_108,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_288])).

tff(c_422,plain,(
    ! [A_109] :
      ( k1_xboole_0 = A_109
      | ~ v3_pre_topc(A_109,'#skF_1')
      | ~ r1_tarski(A_109,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_99,c_407])).

tff(c_425,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_277,c_422])).

tff(c_431,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_425])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_431])).

tff(c_434,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_435,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_670,plain,(
    ! [A_140,B_141] :
      ( k1_tops_1(A_140,B_141) = k1_xboole_0
      | ~ v2_tops_1(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_680,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_670])).

tff(c_687,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_435,c_680])).

tff(c_618,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(k1_tops_1(A_136,B_137),B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_625,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_618])).

tff(c_632,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_625])).

tff(c_690,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_632])).

tff(c_441,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(A_112,B_113)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_445,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_441])).

tff(c_496,plain,(
    ! [A_122,C_123,B_124] :
      ( r1_tarski(A_122,C_123)
      | ~ r1_tarski(B_124,C_123)
      | ~ r1_tarski(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_504,plain,(
    ! [A_122] :
      ( r1_tarski(A_122,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_445,c_496])).

tff(c_714,plain,(
    ! [A_143,B_144] :
      ( v3_pre_topc(k1_tops_1(A_143,B_144),A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_721,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_714])).

tff(c_728,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_687,c_721])).

tff(c_44,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_464,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_44])).

tff(c_26,plain,(
    ! [B_35,D_41,C_39,A_27] :
      ( k1_tops_1(B_35,D_41) = D_41
      | ~ v3_pre_topc(D_41,B_35)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1834,plain,(
    ! [C_214,A_215] :
      ( ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_1841,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_464,c_1834])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1841])).

tff(c_2079,plain,(
    ! [B_223,D_224] :
      ( k1_tops_1(B_223,D_224) = D_224
      | ~ v3_pre_topc(D_224,B_223)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(u1_struct_0(B_223)))
      | ~ l1_pre_topc(B_223) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2278,plain,(
    ! [B_242,A_243] :
      ( k1_tops_1(B_242,A_243) = A_243
      | ~ v3_pre_topc(A_243,B_242)
      | ~ l1_pre_topc(B_242)
      | ~ r1_tarski(A_243,u1_struct_0(B_242)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2079])).

tff(c_2285,plain,(
    ! [A_122] :
      ( k1_tops_1('#skF_1',A_122) = A_122
      | ~ v3_pre_topc(A_122,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_504,c_2278])).

tff(c_2309,plain,(
    ! [A_244] :
      ( k1_tops_1('#skF_1',A_244) = A_244
      | ~ v3_pre_topc(A_244,'#skF_1')
      | ~ r1_tarski(A_244,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2285])).

tff(c_2316,plain,
    ( k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_728,c_2309])).

tff(c_2325,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_2316])).

tff(c_626,plain,(
    ! [A_136,A_13] :
      ( r1_tarski(k1_tops_1(A_136,A_13),A_13)
      | ~ l1_pre_topc(A_136)
      | ~ r1_tarski(A_13,u1_struct_0(A_136)) ) ),
    inference(resolution,[status(thm)],[c_16,c_618])).

tff(c_2338,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2325,c_626])).

tff(c_2352,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2338])).

tff(c_2358,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2352])).

tff(c_2361,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_504,c_2358])).

tff(c_2368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_2361])).

tff(c_2369,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2352])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_468,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_464,c_14])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_472,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_468,c_8])).

tff(c_2370,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2352])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2518,plain,(
    ! [A_248] :
      ( r1_tarski(A_248,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_248,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2370,c_6])).

tff(c_2549,plain,(
    ! [A_248] :
      ( k3_xboole_0(A_248,u1_struct_0('#skF_1')) = A_248
      | ~ r1_tarski(A_248,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2518,c_8])).

tff(c_42,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_439,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_42])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_437,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_40])).

tff(c_2086,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_464,c_2079])).

tff(c_2093,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_437,c_2086])).

tff(c_1706,plain,(
    ! [A_205,B_206,C_207] :
      ( r1_tarski(k1_tops_1(A_205,B_206),k1_tops_1(A_205,C_207))
      | ~ r1_tarski(B_206,C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1729,plain,(
    ! [B_206] :
      ( r1_tarski(k1_tops_1('#skF_1',B_206),k1_xboole_0)
      | ~ r1_tarski(B_206,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_1706])).

tff(c_3287,plain,(
    ! [B_281] :
      ( r1_tarski(k1_tops_1('#skF_1',B_281),k1_xboole_0)
      | ~ r1_tarski(B_281,'#skF_2')
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1729])).

tff(c_3294,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_464,c_3287])).

tff(c_3301,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_2093,c_3294])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_593,plain,(
    ! [A_131,C_132,B_133] :
      ( r1_xboole_0(A_131,C_132)
      | ~ r1_xboole_0(B_133,C_132)
      | ~ r1_tarski(A_131,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_596,plain,(
    ! [A_131,B_2,A_1] :
      ( r1_xboole_0(A_131,B_2)
      | ~ r1_tarski(A_131,A_1)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_593])).

tff(c_3414,plain,(
    ! [B_287] :
      ( r1_xboole_0('#skF_3',B_287)
      | k3_xboole_0(k1_xboole_0,B_287) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3301,c_596])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3433,plain,(
    ! [B_289] :
      ( k3_xboole_0('#skF_3',B_289) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_289) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3414,c_2])).

tff(c_3446,plain,
    ( k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2549,c_3433])).

tff(c_3472,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2369,c_472,c_3446])).

tff(c_3474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_3472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.10  
% 5.54/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.11  %$ v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.54/2.11  
% 5.54/2.11  %Foreground sorts:
% 5.54/2.11  
% 5.54/2.11  
% 5.54/2.11  %Background operators:
% 5.54/2.11  
% 5.54/2.11  
% 5.54/2.11  %Foreground operators:
% 5.54/2.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.54/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.54/2.11  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.54/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.54/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.54/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.54/2.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.54/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.54/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.54/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.54/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.54/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.54/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.54/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.54/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.54/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.54/2.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.54/2.11  
% 5.80/2.13  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 5.80/2.13  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 5.80/2.13  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.80/2.13  tff(f_59, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.80/2.13  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.13  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.80/2.13  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 5.80/2.13  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.80/2.13  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 5.80/2.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.80/2.13  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.80/2.13  tff(c_38, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_57, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 5.80/2.13  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_320, plain, (![B_95, A_96]: (v2_tops_1(B_95, A_96) | k1_tops_1(A_96, B_95)!=k1_xboole_0 | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.80/2.13  tff(c_327, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_320])).
% 5.80/2.13  tff(c_331, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_327])).
% 5.80/2.13  tff(c_332, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_57, c_331])).
% 5.80/2.13  tff(c_146, plain, (![A_79, B_80]: (r1_tarski(k1_tops_1(A_79, B_80), B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.80/2.13  tff(c_151, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_146])).
% 5.80/2.13  tff(c_155, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_151])).
% 5.80/2.13  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_268, plain, (![A_88, B_89]: (v3_pre_topc(k1_tops_1(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.80/2.13  tff(c_273, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_268])).
% 5.80/2.13  tff(c_277, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_273])).
% 5.80/2.13  tff(c_64, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.13  tff(c_68, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_64])).
% 5.80/2.13  tff(c_96, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.13  tff(c_99, plain, (![A_68]: (r1_tarski(A_68, u1_struct_0('#skF_1')) | ~r1_tarski(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_96])).
% 5.80/2.13  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.13  tff(c_56, plain, (![C_52]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_52 | ~v3_pre_topc(C_52, '#skF_1') | ~r1_tarski(C_52, '#skF_2') | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_288, plain, (![C_92]: (k1_xboole_0=C_92 | ~v3_pre_topc(C_92, '#skF_1') | ~r1_tarski(C_92, '#skF_2') | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_57, c_56])).
% 5.80/2.13  tff(c_407, plain, (![A_108]: (k1_xboole_0=A_108 | ~v3_pre_topc(A_108, '#skF_1') | ~r1_tarski(A_108, '#skF_2') | ~r1_tarski(A_108, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_288])).
% 5.80/2.13  tff(c_422, plain, (![A_109]: (k1_xboole_0=A_109 | ~v3_pre_topc(A_109, '#skF_1') | ~r1_tarski(A_109, '#skF_2'))), inference(resolution, [status(thm)], [c_99, c_407])).
% 5.80/2.13  tff(c_425, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_277, c_422])).
% 5.80/2.13  tff(c_431, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_425])).
% 5.80/2.13  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_431])).
% 5.80/2.13  tff(c_434, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 5.80/2.13  tff(c_435, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 5.80/2.13  tff(c_670, plain, (![A_140, B_141]: (k1_tops_1(A_140, B_141)=k1_xboole_0 | ~v2_tops_1(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.80/2.13  tff(c_680, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_670])).
% 5.80/2.13  tff(c_687, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_435, c_680])).
% 5.80/2.13  tff(c_618, plain, (![A_136, B_137]: (r1_tarski(k1_tops_1(A_136, B_137), B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.80/2.13  tff(c_625, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_618])).
% 5.80/2.13  tff(c_632, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_625])).
% 5.80/2.13  tff(c_690, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_632])).
% 5.80/2.13  tff(c_441, plain, (![A_112, B_113]: (r1_tarski(A_112, B_113) | ~m1_subset_1(A_112, k1_zfmisc_1(B_113)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.13  tff(c_445, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_441])).
% 5.80/2.13  tff(c_496, plain, (![A_122, C_123, B_124]: (r1_tarski(A_122, C_123) | ~r1_tarski(B_124, C_123) | ~r1_tarski(A_122, B_124))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.13  tff(c_504, plain, (![A_122]: (r1_tarski(A_122, u1_struct_0('#skF_1')) | ~r1_tarski(A_122, '#skF_2'))), inference(resolution, [status(thm)], [c_445, c_496])).
% 5.80/2.13  tff(c_714, plain, (![A_143, B_144]: (v3_pre_topc(k1_tops_1(A_143, B_144), A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.80/2.13  tff(c_721, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_714])).
% 5.80/2.13  tff(c_728, plain, (v3_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_687, c_721])).
% 5.80/2.13  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_464, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_44])).
% 5.80/2.13  tff(c_26, plain, (![B_35, D_41, C_39, A_27]: (k1_tops_1(B_35, D_41)=D_41 | ~v3_pre_topc(D_41, B_35) | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0(B_35))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.80/2.13  tff(c_1834, plain, (![C_214, A_215]: (~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215))), inference(splitLeft, [status(thm)], [c_26])).
% 5.80/2.13  tff(c_1841, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_464, c_1834])).
% 5.80/2.13  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1841])).
% 5.80/2.13  tff(c_2079, plain, (![B_223, D_224]: (k1_tops_1(B_223, D_224)=D_224 | ~v3_pre_topc(D_224, B_223) | ~m1_subset_1(D_224, k1_zfmisc_1(u1_struct_0(B_223))) | ~l1_pre_topc(B_223))), inference(splitRight, [status(thm)], [c_26])).
% 5.80/2.13  tff(c_2278, plain, (![B_242, A_243]: (k1_tops_1(B_242, A_243)=A_243 | ~v3_pre_topc(A_243, B_242) | ~l1_pre_topc(B_242) | ~r1_tarski(A_243, u1_struct_0(B_242)))), inference(resolution, [status(thm)], [c_16, c_2079])).
% 5.80/2.13  tff(c_2285, plain, (![A_122]: (k1_tops_1('#skF_1', A_122)=A_122 | ~v3_pre_topc(A_122, '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_122, '#skF_2'))), inference(resolution, [status(thm)], [c_504, c_2278])).
% 5.80/2.13  tff(c_2309, plain, (![A_244]: (k1_tops_1('#skF_1', A_244)=A_244 | ~v3_pre_topc(A_244, '#skF_1') | ~r1_tarski(A_244, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2285])).
% 5.80/2.13  tff(c_2316, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_728, c_2309])).
% 5.80/2.13  tff(c_2325, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_690, c_2316])).
% 5.80/2.13  tff(c_626, plain, (![A_136, A_13]: (r1_tarski(k1_tops_1(A_136, A_13), A_13) | ~l1_pre_topc(A_136) | ~r1_tarski(A_13, u1_struct_0(A_136)))), inference(resolution, [status(thm)], [c_16, c_618])).
% 5.80/2.13  tff(c_2338, plain, (r1_tarski(k1_xboole_0, k1_xboole_0) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2325, c_626])).
% 5.80/2.13  tff(c_2352, plain, (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2338])).
% 5.80/2.13  tff(c_2358, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2352])).
% 5.80/2.13  tff(c_2361, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_504, c_2358])).
% 5.80/2.13  tff(c_2368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_690, c_2361])).
% 5.80/2.13  tff(c_2369, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_2352])).
% 5.80/2.13  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.13  tff(c_468, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_464, c_14])).
% 5.80/2.13  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.80/2.13  tff(c_472, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_468, c_8])).
% 5.80/2.13  tff(c_2370, plain, (r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_2352])).
% 5.80/2.13  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.13  tff(c_2518, plain, (![A_248]: (r1_tarski(A_248, u1_struct_0('#skF_1')) | ~r1_tarski(A_248, k1_xboole_0))), inference(resolution, [status(thm)], [c_2370, c_6])).
% 5.80/2.13  tff(c_2549, plain, (![A_248]: (k3_xboole_0(A_248, u1_struct_0('#skF_1'))=A_248 | ~r1_tarski(A_248, k1_xboole_0))), inference(resolution, [status(thm)], [c_2518, c_8])).
% 5.80/2.13  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_439, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_42])).
% 5.80/2.13  tff(c_40, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.80/2.13  tff(c_437, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_40])).
% 5.80/2.13  tff(c_2086, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_464, c_2079])).
% 5.80/2.13  tff(c_2093, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_437, c_2086])).
% 5.80/2.13  tff(c_1706, plain, (![A_205, B_206, C_207]: (r1_tarski(k1_tops_1(A_205, B_206), k1_tops_1(A_205, C_207)) | ~r1_tarski(B_206, C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.80/2.13  tff(c_1729, plain, (![B_206]: (r1_tarski(k1_tops_1('#skF_1', B_206), k1_xboole_0) | ~r1_tarski(B_206, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_687, c_1706])).
% 5.80/2.13  tff(c_3287, plain, (![B_281]: (r1_tarski(k1_tops_1('#skF_1', B_281), k1_xboole_0) | ~r1_tarski(B_281, '#skF_2') | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1729])).
% 5.80/2.13  tff(c_3294, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_464, c_3287])).
% 5.80/2.13  tff(c_3301, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_439, c_2093, c_3294])).
% 5.80/2.13  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.80/2.13  tff(c_593, plain, (![A_131, C_132, B_133]: (r1_xboole_0(A_131, C_132) | ~r1_xboole_0(B_133, C_132) | ~r1_tarski(A_131, B_133))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.13  tff(c_596, plain, (![A_131, B_2, A_1]: (r1_xboole_0(A_131, B_2) | ~r1_tarski(A_131, A_1) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_593])).
% 5.80/2.13  tff(c_3414, plain, (![B_287]: (r1_xboole_0('#skF_3', B_287) | k3_xboole_0(k1_xboole_0, B_287)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3301, c_596])).
% 5.80/2.13  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.80/2.13  tff(c_3433, plain, (![B_289]: (k3_xboole_0('#skF_3', B_289)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_289)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3414, c_2])).
% 5.80/2.13  tff(c_3446, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2549, c_3433])).
% 5.80/2.13  tff(c_3472, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2369, c_472, c_3446])).
% 5.80/2.13  tff(c_3474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_3472])).
% 5.80/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.13  
% 5.80/2.13  Inference rules
% 5.80/2.13  ----------------------
% 5.80/2.13  #Ref     : 0
% 5.80/2.13  #Sup     : 771
% 5.80/2.13  #Fact    : 0
% 5.80/2.13  #Define  : 0
% 5.80/2.13  #Split   : 21
% 5.80/2.13  #Chain   : 0
% 5.80/2.13  #Close   : 0
% 5.80/2.13  
% 5.80/2.13  Ordering : KBO
% 5.80/2.13  
% 5.80/2.13  Simplification rules
% 5.80/2.13  ----------------------
% 5.80/2.13  #Subsume      : 234
% 5.80/2.13  #Demod        : 470
% 5.80/2.13  #Tautology    : 261
% 5.80/2.13  #SimpNegUnit  : 64
% 5.80/2.13  #BackRed      : 29
% 5.80/2.13  
% 5.80/2.13  #Partial instantiations: 0
% 5.80/2.13  #Strategies tried      : 1
% 5.80/2.13  
% 5.80/2.13  Timing (in seconds)
% 5.80/2.13  ----------------------
% 5.80/2.13  Preprocessing        : 0.35
% 5.80/2.13  Parsing              : 0.19
% 5.80/2.13  CNF conversion       : 0.03
% 5.80/2.13  Main loop            : 0.94
% 5.80/2.13  Inferencing          : 0.33
% 5.80/2.13  Reduction            : 0.29
% 5.80/2.13  Demodulation         : 0.19
% 5.80/2.13  BG Simplification    : 0.04
% 5.80/2.13  Subsumption          : 0.21
% 5.80/2.13  Abstraction          : 0.04
% 5.80/2.13  MUC search           : 0.00
% 5.80/2.13  Cooper               : 0.00
% 5.80/2.13  Total                : 1.34
% 5.80/2.13  Index Insertion      : 0.00
% 5.80/2.14  Index Deletion       : 0.00
% 5.80/2.14  Index Matching       : 0.00
% 5.80/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
