%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:24 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  223 (1371 expanded)
%              Number of leaves         :   35 ( 479 expanded)
%              Depth                    :   21
%              Number of atoms          :  469 (5406 expanded)
%              Number of equality atoms :   62 ( 404 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_67,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_58,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_6512,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_67,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_78,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_68,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_389,plain,(
    ! [A_79,B_80] :
      ( k1_tops_1(A_79,k2_pre_topc(A_79,B_80)) = B_80
      | ~ v6_tops_1(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_404,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_389])).

tff(c_419,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_404])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k1_tops_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_454,plain,(
    ! [A_85,B_86] :
      ( v3_pre_topc(k1_tops_1(A_85,k2_pre_topc(A_85,B_86)),A_85)
      | ~ v2_pre_topc(A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_171])).

tff(c_457,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_454])).

tff(c_459,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_52,c_457])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_459])).

tff(c_462,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_464,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_496,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,k2_pre_topc(A_92,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_503,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_496])).

tff(c_510,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_503])).

tff(c_470,plain,(
    ! [A_89,B_90] :
      ( k3_subset_1(A_89,k3_subset_1(A_89,B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_479,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_470])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_463,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_646,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_106),B_105),A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_656,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_646])).

tff(c_662,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_463,c_656])).

tff(c_695,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_698,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_695])).

tff(c_702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_698])).

tff(c_703,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_704,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k2_pre_topc(A_12,B_14) = B_14
      | ~ v4_pre_topc(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_746,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_704,c_18])).

tff(c_759,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_703,c_746])).

tff(c_926,plain,(
    ! [A_125,B_126] :
      ( k3_subset_1(u1_struct_0(A_125),k2_pre_topc(A_125,k3_subset_1(u1_struct_0(A_125),B_126))) = k1_tops_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_953,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_926])).

tff(c_967,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_479,c_953])).

tff(c_665,plain,(
    ! [A_107,B_108] :
      ( k1_tops_1(A_107,k2_pre_topc(A_107,B_108)) = B_108
      | ~ v6_tops_1(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_676,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_665])).

tff(c_685,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_676])).

tff(c_1452,plain,(
    ! [B_133,A_134] :
      ( v4_tops_1(B_133,A_134)
      | ~ r1_tarski(B_133,k2_pre_topc(A_134,k1_tops_1(A_134,B_133)))
      | ~ r1_tarski(k1_tops_1(A_134,k2_pre_topc(A_134,B_133)),B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1467,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_1452])).

tff(c_1476,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_510,c_967,c_1467])).

tff(c_1478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_1476])).

tff(c_1479,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1512,plain,(
    ! [B_139,A_140] :
      ( r1_tarski(B_139,k2_pre_topc(A_140,B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1517,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1512])).

tff(c_1523,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1517])).

tff(c_1480,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_56,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1484,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_1480,c_56])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k1_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1486,plain,(
    ! [A_137,B_138] :
      ( k3_subset_1(A_137,k3_subset_1(A_137,B_138)) = B_138
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1494,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1486])).

tff(c_1662,plain,(
    ! [B_153,A_154] :
      ( v4_pre_topc(B_153,A_154)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_154),B_153),A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1675,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_1662])).

tff(c_1680,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1479,c_1675])).

tff(c_1692,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1680])).

tff(c_1715,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_1692])).

tff(c_1719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1715])).

tff(c_1720,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1680])).

tff(c_1721,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1680])).

tff(c_1746,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1721,c_18])).

tff(c_1756,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1720,c_1746])).

tff(c_1967,plain,(
    ! [A_173,B_174] :
      ( k3_subset_1(u1_struct_0(A_173),k2_pre_topc(A_173,k3_subset_1(u1_struct_0(A_173),B_174))) = k1_tops_1(A_173,B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1994,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_1967])).

tff(c_2011,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1494,c_1994])).

tff(c_2209,plain,(
    ! [A_175,B_176] :
      ( k2_pre_topc(A_175,k1_tops_1(A_175,k2_pre_topc(A_175,k1_tops_1(A_175,B_176)))) = k2_pre_topc(A_175,k1_tops_1(A_175,B_176))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2250,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_2209])).

tff(c_2264,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2011,c_2250])).

tff(c_2294,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2264,c_12])).

tff(c_2315,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2294])).

tff(c_2382,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2315])).

tff(c_2385,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_2382])).

tff(c_2388,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2385])).

tff(c_2432,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_2388])).

tff(c_2436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2432])).

tff(c_2437,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2315])).

tff(c_2568,plain,(
    ! [B_180,A_181,C_182] :
      ( r1_tarski(B_180,k1_tops_1(A_181,C_182))
      | ~ r1_tarski(B_180,C_182)
      | ~ v3_pre_topc(B_180,A_181)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2574,plain,(
    ! [B_180] :
      ( r1_tarski(B_180,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_180,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_180,'#skF_2')
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2437,c_2568])).

tff(c_2602,plain,(
    ! [B_180] :
      ( r1_tarski(B_180,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_180,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_180,'#skF_2')
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2574])).

tff(c_1948,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(k1_tops_1(A_171,k2_pre_topc(A_171,B_172)),B_172)
      | ~ v4_tops_1(B_172,A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4316,plain,(
    ! [A_219,B_220] :
      ( k1_tops_1(A_219,k2_pre_topc(A_219,B_220)) = B_220
      | ~ r1_tarski(B_220,k1_tops_1(A_219,k2_pre_topc(A_219,B_220)))
      | ~ v4_tops_1(B_220,A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(resolution,[status(thm)],[c_1948,c_2])).

tff(c_4320,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2602,c_4316])).

tff(c_4344,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1479,c_1523,c_48,c_1484,c_4320])).

tff(c_2438,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2315])).

tff(c_28,plain,(
    ! [B_23,A_21] :
      ( v6_tops_1(B_23,A_21)
      | k1_tops_1(A_21,k2_pre_topc(A_21,B_23)) != B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2291,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2264,c_28])).

tff(c_2313,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2291])).

tff(c_2742,plain,(
    v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_2313])).

tff(c_4370,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4344,c_2742])).

tff(c_4380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_4370])).

tff(c_4381,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4420,plain,(
    ! [B_227,A_228] :
      ( r1_tarski(B_227,k2_pre_topc(A_228,B_227))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4425,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_4420])).

tff(c_4431,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4425])).

tff(c_4382,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4383,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_4382,c_62])).

tff(c_4394,plain,(
    ! [A_225,B_226] :
      ( k3_subset_1(A_225,k3_subset_1(A_225,B_226)) = B_226
      | ~ m1_subset_1(B_226,k1_zfmisc_1(A_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4402,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_4394])).

tff(c_4570,plain,(
    ! [B_241,A_242] :
      ( v4_pre_topc(B_241,A_242)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_242),B_241),A_242)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4583,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4402,c_4570])).

tff(c_4588,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4381,c_4583])).

tff(c_4617,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4588])).

tff(c_4620,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_4617])).

tff(c_4624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4620])).

tff(c_4625,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4588])).

tff(c_4626,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4588])).

tff(c_4668,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4626,c_18])).

tff(c_4680,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4625,c_4668])).

tff(c_4865,plain,(
    ! [A_265,B_266] :
      ( k3_subset_1(u1_struct_0(A_265),k2_pre_topc(A_265,k3_subset_1(u1_struct_0(A_265),B_266))) = k1_tops_1(A_265,B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4901,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4680,c_4865])).

tff(c_4915,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_4402,c_4901])).

tff(c_4949,plain,(
    ! [A_267,B_268] :
      ( k2_pre_topc(A_267,k1_tops_1(A_267,k2_pre_topc(A_267,k1_tops_1(A_267,B_268)))) = k2_pre_topc(A_267,k1_tops_1(A_267,B_268))
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4987,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4915,c_4949])).

tff(c_4996,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_4915,c_4987])).

tff(c_5020,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4996,c_28])).

tff(c_5042,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5020])).

tff(c_5566,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5042])).

tff(c_5569,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_5566])).

tff(c_5572,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5569])).

tff(c_5610,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5572])).

tff(c_5614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_5610])).

tff(c_5616,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5042])).

tff(c_5023,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4996,c_12])).

tff(c_5044,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5023])).

tff(c_5715,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5616,c_5044])).

tff(c_40,plain,(
    ! [B_35,A_31,C_37] :
      ( r1_tarski(B_35,k1_tops_1(A_31,C_37))
      | ~ r1_tarski(B_35,C_37)
      | ~ v3_pre_topc(B_35,A_31)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5717,plain,(
    ! [B_35] :
      ( r1_tarski(B_35,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_35,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_35,'#skF_2')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5715,c_40])).

tff(c_5734,plain,(
    ! [B_35] :
      ( r1_tarski(B_35,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_35,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_35,'#skF_2')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5717])).

tff(c_4796,plain,(
    ! [A_257,B_258] :
      ( r1_tarski(k1_tops_1(A_257,k2_pre_topc(A_257,B_258)),B_258)
      | ~ v4_tops_1(B_258,A_257)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6446,plain,(
    ! [A_299,B_300] :
      ( k1_tops_1(A_299,k2_pre_topc(A_299,B_300)) = B_300
      | ~ r1_tarski(B_300,k1_tops_1(A_299,k2_pre_topc(A_299,B_300)))
      | ~ v4_tops_1(B_300,A_299)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(resolution,[status(thm)],[c_4796,c_2])).

tff(c_6450,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_5734,c_6446])).

tff(c_6472,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4381,c_4431,c_48,c_4383,c_6450])).

tff(c_5615,plain,(
    v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5042])).

tff(c_6494,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6472,c_5615])).

tff(c_6500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_6494])).

tff(c_6501,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6724,plain,(
    ! [A_323,B_324] :
      ( k1_tops_1(A_323,k2_pre_topc(A_323,B_324)) = B_324
      | ~ v6_tops_1(B_324,A_323)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6737,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_6724])).

tff(c_6749,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6501,c_6737])).

tff(c_6579,plain,(
    ! [A_313,B_314] :
      ( v3_pre_topc(k1_tops_1(A_313,B_314),A_313)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6926,plain,(
    ! [A_335,B_336] :
      ( v3_pre_topc(k1_tops_1(A_335,k2_pre_topc(A_335,B_336)),A_335)
      | ~ v2_pre_topc(A_335)
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ l1_pre_topc(A_335) ) ),
    inference(resolution,[status(thm)],[c_12,c_6579])).

tff(c_6929,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6749,c_6926])).

tff(c_6934,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_52,c_6929])).

tff(c_6936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6512,c_6934])).

tff(c_6938,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6937,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6939,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6937])).

tff(c_6972,plain,(
    ! [B_341,A_342] :
      ( r1_tarski(B_341,k2_pre_topc(A_342,B_341))
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6979,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_6972])).

tff(c_6986,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6979])).

tff(c_6945,plain,(
    ! [A_337,B_338] :
      ( k3_subset_1(A_337,k3_subset_1(A_337,B_338)) = B_338
      | ~ m1_subset_1(B_338,k1_zfmisc_1(A_337)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6951,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_6945])).

tff(c_7059,plain,(
    ! [B_351,A_352] :
      ( v4_pre_topc(B_351,A_352)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_352),B_351),A_352)
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ l1_pre_topc(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7062,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6951,c_7059])).

tff(c_7067,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6938,c_7062])).

tff(c_7122,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7067])).

tff(c_7125,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_7122])).

tff(c_7129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7125])).

tff(c_7130,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_7067])).

tff(c_7131,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7067])).

tff(c_7166,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_7131,c_18])).

tff(c_7176,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7130,c_7166])).

tff(c_7458,plain,(
    ! [A_377,B_378] :
      ( k3_subset_1(u1_struct_0(A_377),k2_pre_topc(A_377,k3_subset_1(u1_struct_0(A_377),B_378))) = k1_tops_1(A_377,B_378)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7488,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7176,c_7458])).

tff(c_7502,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6951,c_7488])).

tff(c_7281,plain,(
    ! [A_361,B_362] :
      ( k1_tops_1(A_361,k2_pre_topc(A_361,B_362)) = B_362
      | ~ v6_tops_1(B_362,A_361)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7296,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_7281])).

tff(c_7311,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6501,c_7296])).

tff(c_8015,plain,(
    ! [B_385,A_386] :
      ( v4_tops_1(B_385,A_386)
      | ~ r1_tarski(B_385,k2_pre_topc(A_386,k1_tops_1(A_386,B_385)))
      | ~ r1_tarski(k1_tops_1(A_386,k2_pre_topc(A_386,B_385)),B_385)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8027,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7311,c_8015])).

tff(c_8040,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_6986,c_7502,c_8027])).

tff(c_8042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6939,c_8040])).

tff(c_8044,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_6937])).

tff(c_6502,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_8048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6938,c_8044,c_6502,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.54/3.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.79/4.01  
% 11.79/4.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.79/4.01  %$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.79/4.01  
% 11.79/4.01  %Foreground sorts:
% 11.79/4.01  
% 11.79/4.01  
% 11.79/4.01  %Background operators:
% 11.79/4.01  
% 11.79/4.01  
% 11.79/4.01  %Foreground operators:
% 11.79/4.01  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.79/4.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.79/4.01  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 11.79/4.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.79/4.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.79/4.01  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.79/4.01  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 11.79/4.01  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.79/4.01  tff('#skF_2', type, '#skF_2': $i).
% 11.79/4.01  tff('#skF_3', type, '#skF_3': $i).
% 11.79/4.01  tff('#skF_1', type, '#skF_1': $i).
% 11.79/4.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.79/4.01  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.79/4.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.79/4.01  tff('#skF_4', type, '#skF_4': $i).
% 11.79/4.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.79/4.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.79/4.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.79/4.01  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.79/4.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.79/4.01  
% 12.09/4.06  tff(f_164, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 12.09/4.06  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 12.09/4.06  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 12.09/4.06  tff(f_108, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 12.09/4.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.09/4.06  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 12.09/4.06  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.09/4.06  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 12.09/4.06  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 12.09/4.06  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 12.09/4.06  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 12.09/4.06  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 12.09/4.06  tff(f_100, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 12.09/4.06  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tops_1)).
% 12.09/4.06  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 12.09/4.06  tff(c_58, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_6512, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 12.09/4.06  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_60, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_67, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 12.09/4.06  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_78, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 12.09/4.06  tff(c_64, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_68, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 12.09/4.06  tff(c_389, plain, (![A_79, B_80]: (k1_tops_1(A_79, k2_pre_topc(A_79, B_80))=B_80 | ~v6_tops_1(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.09/4.06  tff(c_404, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_389])).
% 12.09/4.06  tff(c_419, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_404])).
% 12.09/4.06  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.09/4.06  tff(c_171, plain, (![A_67, B_68]: (v3_pre_topc(k1_tops_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.09/4.06  tff(c_454, plain, (![A_85, B_86]: (v3_pre_topc(k1_tops_1(A_85, k2_pre_topc(A_85, B_86)), A_85) | ~v2_pre_topc(A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_12, c_171])).
% 12.09/4.06  tff(c_457, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_419, c_454])).
% 12.09/4.06  tff(c_459, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_52, c_457])).
% 12.09/4.06  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_459])).
% 12.09/4.06  tff(c_462, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 12.09/4.06  tff(c_464, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_462])).
% 12.09/4.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.09/4.06  tff(c_496, plain, (![B_91, A_92]: (r1_tarski(B_91, k2_pre_topc(A_92, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.09/4.06  tff(c_503, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_496])).
% 12.09/4.06  tff(c_510, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_503])).
% 12.09/4.06  tff(c_470, plain, (![A_89, B_90]: (k3_subset_1(A_89, k3_subset_1(A_89, B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.09/4.06  tff(c_479, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_470])).
% 12.09/4.06  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.09/4.06  tff(c_463, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 12.09/4.06  tff(c_646, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_106), B_105), A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.09/4.06  tff(c_656, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_479, c_646])).
% 12.09/4.06  tff(c_662, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_463, c_656])).
% 12.09/4.06  tff(c_695, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_662])).
% 12.09/4.06  tff(c_698, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_695])).
% 12.09/4.06  tff(c_702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_698])).
% 12.09/4.06  tff(c_703, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_662])).
% 12.09/4.06  tff(c_704, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_662])).
% 12.09/4.06  tff(c_18, plain, (![A_12, B_14]: (k2_pre_topc(A_12, B_14)=B_14 | ~v4_pre_topc(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.09/4.06  tff(c_746, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_704, c_18])).
% 12.09/4.06  tff(c_759, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_703, c_746])).
% 12.09/4.06  tff(c_926, plain, (![A_125, B_126]: (k3_subset_1(u1_struct_0(A_125), k2_pre_topc(A_125, k3_subset_1(u1_struct_0(A_125), B_126)))=k1_tops_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.09/4.06  tff(c_953, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_759, c_926])).
% 12.09/4.06  tff(c_967, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_479, c_953])).
% 12.09/4.06  tff(c_665, plain, (![A_107, B_108]: (k1_tops_1(A_107, k2_pre_topc(A_107, B_108))=B_108 | ~v6_tops_1(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.09/4.06  tff(c_676, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_665])).
% 12.09/4.06  tff(c_685, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_676])).
% 12.09/4.06  tff(c_1452, plain, (![B_133, A_134]: (v4_tops_1(B_133, A_134) | ~r1_tarski(B_133, k2_pre_topc(A_134, k1_tops_1(A_134, B_133))) | ~r1_tarski(k1_tops_1(A_134, k2_pre_topc(A_134, B_133)), B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.09/4.06  tff(c_1467, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_685, c_1452])).
% 12.09/4.06  tff(c_1476, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_510, c_967, c_1467])).
% 12.09/4.06  tff(c_1478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_464, c_1476])).
% 12.09/4.06  tff(c_1479, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_462])).
% 12.09/4.06  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_1512, plain, (![B_139, A_140]: (r1_tarski(B_139, k2_pre_topc(A_140, B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.09/4.06  tff(c_1517, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1512])).
% 12.09/4.06  tff(c_1523, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1517])).
% 12.09/4.06  tff(c_1480, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_462])).
% 12.09/4.06  tff(c_56, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_1484, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_1480, c_56])).
% 12.09/4.06  tff(c_32, plain, (![A_24, B_25]: (m1_subset_1(k1_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.09/4.06  tff(c_1486, plain, (![A_137, B_138]: (k3_subset_1(A_137, k3_subset_1(A_137, B_138))=B_138 | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.09/4.06  tff(c_1494, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1486])).
% 12.09/4.06  tff(c_1662, plain, (![B_153, A_154]: (v4_pre_topc(B_153, A_154) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_154), B_153), A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.09/4.06  tff(c_1675, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1494, c_1662])).
% 12.09/4.06  tff(c_1680, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1479, c_1675])).
% 12.09/4.06  tff(c_1692, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1680])).
% 12.09/4.06  tff(c_1715, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_1692])).
% 12.09/4.06  tff(c_1719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1715])).
% 12.09/4.06  tff(c_1720, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_1680])).
% 12.09/4.06  tff(c_1721, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1680])).
% 12.09/4.06  tff(c_1746, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1721, c_18])).
% 12.09/4.06  tff(c_1756, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1720, c_1746])).
% 12.09/4.06  tff(c_1967, plain, (![A_173, B_174]: (k3_subset_1(u1_struct_0(A_173), k2_pre_topc(A_173, k3_subset_1(u1_struct_0(A_173), B_174)))=k1_tops_1(A_173, B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.09/4.06  tff(c_1994, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_1967])).
% 12.09/4.06  tff(c_2011, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1494, c_1994])).
% 12.09/4.06  tff(c_2209, plain, (![A_175, B_176]: (k2_pre_topc(A_175, k1_tops_1(A_175, k2_pre_topc(A_175, k1_tops_1(A_175, B_176))))=k2_pre_topc(A_175, k1_tops_1(A_175, B_176)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.09/4.06  tff(c_2250, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2011, c_2209])).
% 12.09/4.06  tff(c_2264, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2011, c_2250])).
% 12.09/4.06  tff(c_2294, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2264, c_12])).
% 12.09/4.06  tff(c_2315, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2294])).
% 12.09/4.06  tff(c_2382, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2315])).
% 12.09/4.06  tff(c_2385, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_2382])).
% 12.09/4.06  tff(c_2388, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2385])).
% 12.09/4.06  tff(c_2432, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_2388])).
% 12.09/4.06  tff(c_2436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2432])).
% 12.09/4.06  tff(c_2437, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2315])).
% 12.09/4.06  tff(c_2568, plain, (![B_180, A_181, C_182]: (r1_tarski(B_180, k1_tops_1(A_181, C_182)) | ~r1_tarski(B_180, C_182) | ~v3_pre_topc(B_180, A_181) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.09/4.06  tff(c_2574, plain, (![B_180]: (r1_tarski(B_180, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_180, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_180, '#skF_2') | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2437, c_2568])).
% 12.09/4.06  tff(c_2602, plain, (![B_180]: (r1_tarski(B_180, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_180, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_180, '#skF_2') | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2574])).
% 12.09/4.06  tff(c_1948, plain, (![A_171, B_172]: (r1_tarski(k1_tops_1(A_171, k2_pre_topc(A_171, B_172)), B_172) | ~v4_tops_1(B_172, A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.09/4.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.09/4.06  tff(c_4316, plain, (![A_219, B_220]: (k1_tops_1(A_219, k2_pre_topc(A_219, B_220))=B_220 | ~r1_tarski(B_220, k1_tops_1(A_219, k2_pre_topc(A_219, B_220))) | ~v4_tops_1(B_220, A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(resolution, [status(thm)], [c_1948, c_2])).
% 12.09/4.06  tff(c_4320, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2602, c_4316])).
% 12.09/4.06  tff(c_4344, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1479, c_1523, c_48, c_1484, c_4320])).
% 12.09/4.06  tff(c_2438, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2315])).
% 12.09/4.06  tff(c_28, plain, (![B_23, A_21]: (v6_tops_1(B_23, A_21) | k1_tops_1(A_21, k2_pre_topc(A_21, B_23))!=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.09/4.06  tff(c_2291, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2264, c_28])).
% 12.09/4.06  tff(c_2313, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2291])).
% 12.09/4.06  tff(c_2742, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2438, c_2313])).
% 12.09/4.06  tff(c_4370, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4344, c_2742])).
% 12.09/4.06  tff(c_4380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_4370])).
% 12.09/4.06  tff(c_4381, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 12.09/4.06  tff(c_4420, plain, (![B_227, A_228]: (r1_tarski(B_227, k2_pre_topc(A_228, B_227)) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.09/4.06  tff(c_4425, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_4420])).
% 12.09/4.06  tff(c_4431, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4425])).
% 12.09/4.06  tff(c_4382, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 12.09/4.06  tff(c_62, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_4383, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_4382, c_62])).
% 12.09/4.06  tff(c_4394, plain, (![A_225, B_226]: (k3_subset_1(A_225, k3_subset_1(A_225, B_226))=B_226 | ~m1_subset_1(B_226, k1_zfmisc_1(A_225)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.09/4.06  tff(c_4402, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_44, c_4394])).
% 12.09/4.06  tff(c_4570, plain, (![B_241, A_242]: (v4_pre_topc(B_241, A_242) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_242), B_241), A_242) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.09/4.06  tff(c_4583, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4402, c_4570])).
% 12.09/4.06  tff(c_4588, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4381, c_4583])).
% 12.09/4.06  tff(c_4617, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_4588])).
% 12.09/4.06  tff(c_4620, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_4617])).
% 12.09/4.06  tff(c_4624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_4620])).
% 12.09/4.06  tff(c_4625, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_4588])).
% 12.09/4.06  tff(c_4626, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_4588])).
% 12.09/4.06  tff(c_4668, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4626, c_18])).
% 12.09/4.06  tff(c_4680, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4625, c_4668])).
% 12.09/4.06  tff(c_4865, plain, (![A_265, B_266]: (k3_subset_1(u1_struct_0(A_265), k2_pre_topc(A_265, k3_subset_1(u1_struct_0(A_265), B_266)))=k1_tops_1(A_265, B_266) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.09/4.06  tff(c_4901, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4680, c_4865])).
% 12.09/4.06  tff(c_4915, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_4402, c_4901])).
% 12.09/4.06  tff(c_4949, plain, (![A_267, B_268]: (k2_pre_topc(A_267, k1_tops_1(A_267, k2_pre_topc(A_267, k1_tops_1(A_267, B_268))))=k2_pre_topc(A_267, k1_tops_1(A_267, B_268)) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.09/4.06  tff(c_4987, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4915, c_4949])).
% 12.09/4.06  tff(c_4996, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_4915, c_4987])).
% 12.09/4.06  tff(c_5020, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4996, c_28])).
% 12.09/4.06  tff(c_5042, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5020])).
% 12.09/4.06  tff(c_5566, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_5042])).
% 12.09/4.06  tff(c_5569, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_5566])).
% 12.09/4.06  tff(c_5572, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5569])).
% 12.09/4.06  tff(c_5610, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5572])).
% 12.09/4.06  tff(c_5614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_5610])).
% 12.09/4.06  tff(c_5616, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_5042])).
% 12.09/4.06  tff(c_5023, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4996, c_12])).
% 12.09/4.06  tff(c_5044, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5023])).
% 12.09/4.06  tff(c_5715, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5616, c_5044])).
% 12.09/4.06  tff(c_40, plain, (![B_35, A_31, C_37]: (r1_tarski(B_35, k1_tops_1(A_31, C_37)) | ~r1_tarski(B_35, C_37) | ~v3_pre_topc(B_35, A_31) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.09/4.06  tff(c_5717, plain, (![B_35]: (r1_tarski(B_35, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_35, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_35, '#skF_2') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_5715, c_40])).
% 12.09/4.06  tff(c_5734, plain, (![B_35]: (r1_tarski(B_35, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_35, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_35, '#skF_2') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5717])).
% 12.09/4.06  tff(c_4796, plain, (![A_257, B_258]: (r1_tarski(k1_tops_1(A_257, k2_pre_topc(A_257, B_258)), B_258) | ~v4_tops_1(B_258, A_257) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.09/4.06  tff(c_6446, plain, (![A_299, B_300]: (k1_tops_1(A_299, k2_pre_topc(A_299, B_300))=B_300 | ~r1_tarski(B_300, k1_tops_1(A_299, k2_pre_topc(A_299, B_300))) | ~v4_tops_1(B_300, A_299) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299))), inference(resolution, [status(thm)], [c_4796, c_2])).
% 12.09/4.06  tff(c_6450, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_5734, c_6446])).
% 12.09/4.06  tff(c_6472, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4381, c_4431, c_48, c_4383, c_6450])).
% 12.09/4.06  tff(c_5615, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_5042])).
% 12.09/4.06  tff(c_6494, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6472, c_5615])).
% 12.09/4.06  tff(c_6500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_6494])).
% 12.09/4.06  tff(c_6501, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 12.09/4.06  tff(c_6724, plain, (![A_323, B_324]: (k1_tops_1(A_323, k2_pre_topc(A_323, B_324))=B_324 | ~v6_tops_1(B_324, A_323) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.09/4.06  tff(c_6737, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_6724])).
% 12.09/4.06  tff(c_6749, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6501, c_6737])).
% 12.09/4.06  tff(c_6579, plain, (![A_313, B_314]: (v3_pre_topc(k1_tops_1(A_313, B_314), A_313) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.09/4.06  tff(c_6926, plain, (![A_335, B_336]: (v3_pre_topc(k1_tops_1(A_335, k2_pre_topc(A_335, B_336)), A_335) | ~v2_pre_topc(A_335) | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(A_335))) | ~l1_pre_topc(A_335))), inference(resolution, [status(thm)], [c_12, c_6579])).
% 12.09/4.06  tff(c_6929, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6749, c_6926])).
% 12.09/4.06  tff(c_6934, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_52, c_6929])).
% 12.09/4.06  tff(c_6936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6512, c_6934])).
% 12.09/4.06  tff(c_6938, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 12.09/4.06  tff(c_6937, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 12.09/4.06  tff(c_6939, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_6937])).
% 12.09/4.06  tff(c_6972, plain, (![B_341, A_342]: (r1_tarski(B_341, k2_pre_topc(A_342, B_341)) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_342))) | ~l1_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.09/4.06  tff(c_6979, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_6972])).
% 12.09/4.06  tff(c_6986, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6979])).
% 12.09/4.06  tff(c_6945, plain, (![A_337, B_338]: (k3_subset_1(A_337, k3_subset_1(A_337, B_338))=B_338 | ~m1_subset_1(B_338, k1_zfmisc_1(A_337)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.09/4.06  tff(c_6951, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_6945])).
% 12.09/4.06  tff(c_7059, plain, (![B_351, A_352]: (v4_pre_topc(B_351, A_352) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_352), B_351), A_352) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_352))) | ~l1_pre_topc(A_352))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.09/4.06  tff(c_7062, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6951, c_7059])).
% 12.09/4.06  tff(c_7067, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6938, c_7062])).
% 12.09/4.06  tff(c_7122, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7067])).
% 12.09/4.06  tff(c_7125, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_7122])).
% 12.09/4.06  tff(c_7129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_7125])).
% 12.09/4.06  tff(c_7130, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_7067])).
% 12.09/4.06  tff(c_7131, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7067])).
% 12.09/4.06  tff(c_7166, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_7131, c_18])).
% 12.09/4.06  tff(c_7176, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7130, c_7166])).
% 12.09/4.06  tff(c_7458, plain, (![A_377, B_378]: (k3_subset_1(u1_struct_0(A_377), k2_pre_topc(A_377, k3_subset_1(u1_struct_0(A_377), B_378)))=k1_tops_1(A_377, B_378) | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.09/4.06  tff(c_7488, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7176, c_7458])).
% 12.09/4.06  tff(c_7502, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6951, c_7488])).
% 12.09/4.06  tff(c_7281, plain, (![A_361, B_362]: (k1_tops_1(A_361, k2_pre_topc(A_361, B_362))=B_362 | ~v6_tops_1(B_362, A_361) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_pre_topc(A_361))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.09/4.06  tff(c_7296, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_7281])).
% 12.09/4.06  tff(c_7311, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6501, c_7296])).
% 12.09/4.06  tff(c_8015, plain, (![B_385, A_386]: (v4_tops_1(B_385, A_386) | ~r1_tarski(B_385, k2_pre_topc(A_386, k1_tops_1(A_386, B_385))) | ~r1_tarski(k1_tops_1(A_386, k2_pre_topc(A_386, B_385)), B_385) | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0(A_386))) | ~l1_pre_topc(A_386))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.09/4.06  tff(c_8027, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7311, c_8015])).
% 12.09/4.06  tff(c_8040, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_6986, c_7502, c_8027])).
% 12.09/4.06  tff(c_8042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6939, c_8040])).
% 12.09/4.06  tff(c_8044, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_6937])).
% 12.09/4.06  tff(c_6502, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 12.09/4.06  tff(c_54, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 12.09/4.06  tff(c_8048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6938, c_8044, c_6502, c_54])).
% 12.09/4.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.09/4.06  
% 12.09/4.06  Inference rules
% 12.09/4.06  ----------------------
% 12.09/4.06  #Ref     : 0
% 12.09/4.06  #Sup     : 1673
% 12.09/4.06  #Fact    : 0
% 12.09/4.06  #Define  : 0
% 12.09/4.06  #Split   : 110
% 12.09/4.06  #Chain   : 0
% 12.09/4.06  #Close   : 0
% 12.09/4.06  
% 12.09/4.06  Ordering : KBO
% 12.09/4.06  
% 12.09/4.06  Simplification rules
% 12.09/4.06  ----------------------
% 12.09/4.06  #Subsume      : 244
% 12.09/4.06  #Demod        : 2498
% 12.09/4.06  #Tautology    : 624
% 12.09/4.06  #SimpNegUnit  : 99
% 12.09/4.06  #BackRed      : 41
% 12.09/4.06  
% 12.09/4.06  #Partial instantiations: 0
% 12.09/4.06  #Strategies tried      : 1
% 12.09/4.06  
% 12.09/4.06  Timing (in seconds)
% 12.09/4.06  ----------------------
% 12.16/4.07  Preprocessing        : 0.56
% 12.16/4.07  Parsing              : 0.30
% 12.16/4.07  CNF conversion       : 0.05
% 12.16/4.07  Main loop            : 2.53
% 12.16/4.07  Inferencing          : 0.80
% 12.16/4.07  Reduction            : 1.00
% 12.16/4.07  Demodulation         : 0.73
% 12.16/4.07  BG Simplification    : 0.09
% 12.16/4.07  Subsumption          : 0.46
% 12.16/4.07  Abstraction          : 0.11
% 12.16/4.07  MUC search           : 0.00
% 12.16/4.07  Cooper               : 0.00
% 12.16/4.07  Total                : 3.21
% 12.16/4.07  Index Insertion      : 0.00
% 12.16/4.07  Index Deletion       : 0.00
% 12.16/4.07  Index Matching       : 0.00
% 12.16/4.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
