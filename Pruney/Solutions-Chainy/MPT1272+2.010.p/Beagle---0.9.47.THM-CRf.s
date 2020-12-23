%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:59 EST 2020

% Result     : Theorem 52.03s
% Output     : CNFRefutation 52.03s
% Verified   : 
% Statistics : Number of formulae       :  210 (2264 expanded)
%              Number of leaves         :   41 ( 779 expanded)
%              Depth                    :   29
%              Number of atoms          :  439 (4700 expanded)
%              Number of equality atoms :   61 ( 722 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_34,c_82])).

tff(c_101,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_97])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_104,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64])).

tff(c_1087,plain,(
    ! [B_125,A_126] :
      ( v2_tops_1(B_125,A_126)
      | k1_tops_1(A_126,B_125) != k1_xboole_0
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1105,plain,(
    ! [B_125] :
      ( v2_tops_1(B_125,'#skF_1')
      | k1_tops_1('#skF_1',B_125) != k1_xboole_0
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1087])).

tff(c_1146,plain,(
    ! [B_130] :
      ( v2_tops_1(B_130,'#skF_1')
      | k1_tops_1('#skF_1',B_130) != k1_xboole_0
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1105])).

tff(c_1169,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_1146])).

tff(c_1170,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1169])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_167,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k3_subset_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k3_subset_1(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_167,c_26])).

tff(c_849,plain,(
    ! [A_114,B_115] :
      ( k2_subset_1(A_114) = B_115
      | ~ r1_tarski(k3_subset_1(A_114,B_115),B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_884,plain,(
    ! [A_116] :
      ( k2_subset_1(A_116) = A_116
      | ~ m1_subset_1(A_116,k1_zfmisc_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_174,c_849])).

tff(c_888,plain,(
    ! [B_23] :
      ( k2_subset_1(B_23) = B_23
      | ~ r1_tarski(B_23,B_23) ) ),
    inference(resolution,[status(thm)],[c_28,c_884])).

tff(c_891,plain,(
    ! [B_23] : k2_subset_1(B_23) = B_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_888])).

tff(c_306,plain,(
    ! [A_88,B_89] :
      ( k3_subset_1(A_88,k3_subset_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_317,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_104,c_306])).

tff(c_863,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_subset_1(k2_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_849])).

tff(c_18451,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_863])).

tff(c_18452,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_18451])).

tff(c_18455,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_18452])).

tff(c_18462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_18455])).

tff(c_18464,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_18451])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_pre_topc(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19480,plain,(
    ! [A_480,B_481] :
      ( k3_subset_1(u1_struct_0(A_480),k2_pre_topc(A_480,k3_subset_1(u1_struct_0(A_480),B_481))) = k1_tops_1(A_480,B_481)
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ l1_pre_topc(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_27768,plain,(
    ! [A_621,B_622] :
      ( m1_subset_1(k1_tops_1(A_621,B_622),k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ m1_subset_1(k2_pre_topc(A_621,k3_subset_1(u1_struct_0(A_621),B_622)),k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ m1_subset_1(B_622,k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ l1_pre_topc(A_621) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19480,c_12])).

tff(c_57915,plain,(
    ! [A_960,B_961] :
      ( m1_subset_1(k1_tops_1(A_960,B_961),k1_zfmisc_1(u1_struct_0(A_960)))
      | ~ m1_subset_1(B_961,k1_zfmisc_1(u1_struct_0(A_960)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_960),B_961),k1_zfmisc_1(u1_struct_0(A_960)))
      | ~ l1_pre_topc(A_960) ) ),
    inference(resolution,[status(thm)],[c_32,c_27768])).

tff(c_57950,plain,(
    ! [B_961] :
      ( m1_subset_1(k1_tops_1('#skF_1',B_961),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_961,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),B_961),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_57915])).

tff(c_58221,plain,(
    ! [B_963] :
      ( m1_subset_1(k1_tops_1('#skF_1',B_963),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_963,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_963),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_101,c_101,c_57950])).

tff(c_58264,plain,
    ( m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_58221])).

tff(c_58285,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_18464,c_58264])).

tff(c_19532,plain,(
    ! [B_481] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_481))) = k1_tops_1('#skF_1',B_481)
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_19480])).

tff(c_19671,plain,(
    ! [B_484] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_484))) = k1_tops_1('#skF_1',B_484)
      | ~ m1_subset_1(B_484,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_101,c_19532])).

tff(c_19720,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_19671])).

tff(c_19726,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18464,c_19720])).

tff(c_998,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k2_pre_topc(A_121,B_122),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_subset_1(A_9,k3_subset_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25014,plain,(
    ! [A_570,B_571] :
      ( k3_subset_1(u1_struct_0(A_570),k3_subset_1(u1_struct_0(A_570),k2_pre_topc(A_570,B_571))) = k2_pre_topc(A_570,B_571)
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0(A_570)))
      | ~ l1_pre_topc(A_570) ) ),
    inference(resolution,[status(thm)],[c_998,c_14])).

tff(c_25093,plain,(
    ! [B_571] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_571))) = k2_pre_topc('#skF_1',B_571)
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_25014])).

tff(c_25110,plain,(
    ! [B_571] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_571))) = k2_pre_topc('#skF_1',B_571)
      | ~ m1_subset_1(B_571,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_101,c_25093])).

tff(c_36901,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19726,c_25110])).

tff(c_36965,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_36901])).

tff(c_68955,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36965,c_12])).

tff(c_69046,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58285,c_68955])).

tff(c_62,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1290,plain,(
    ! [A_139,B_140] :
      ( v2_tops_1(k2_pre_topc(A_139,B_140),A_139)
      | ~ v3_tops_1(B_140,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1303,plain,(
    ! [B_140] :
      ( v2_tops_1(k2_pre_topc('#skF_1',B_140),'#skF_1')
      | ~ v3_tops_1(B_140,'#skF_1')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1290])).

tff(c_1318,plain,(
    ! [B_141] :
      ( v2_tops_1(k2_pre_topc('#skF_1',B_141),'#skF_1')
      | ~ v3_tops_1(B_141,'#skF_1')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1303])).

tff(c_1336,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_1318])).

tff(c_1343,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1336])).

tff(c_1190,plain,(
    ! [A_133,B_134] :
      ( k1_tops_1(A_133,B_134) = k1_xboole_0
      | ~ v2_tops_1(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_23525,plain,(
    ! [A_540,B_541] :
      ( k1_tops_1(A_540,k2_pre_topc(A_540,B_541)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_540,B_541),A_540)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(u1_struct_0(A_540)))
      | ~ l1_pre_topc(A_540) ) ),
    inference(resolution,[status(thm)],[c_32,c_1190])).

tff(c_23534,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1343,c_23525])).

tff(c_23544,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_104,c_101,c_23534])).

tff(c_533,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,k2_pre_topc(A_102,B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_541,plain,(
    ! [B_101] :
      ( r1_tarski(B_101,k2_pre_topc('#skF_1',B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_533])).

tff(c_668,plain,(
    ! [B_107] :
      ( r1_tarski(B_107,k2_pre_topc('#skF_1',B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_541])).

tff(c_682,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_668])).

tff(c_54,plain,(
    ! [A_46,B_50,C_52] :
      ( r1_tarski(k1_tops_1(A_46,B_50),k1_tops_1(A_46,C_52))
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_19960,plain,(
    ! [A_488,B_489,C_490] :
      ( r1_tarski(k1_tops_1(A_488,B_489),k1_tops_1(A_488,C_490))
      | ~ r1_tarski(B_489,C_490)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ m1_subset_1(B_489,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ l1_pre_topc(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28184,plain,(
    ! [A_629,A_630,C_631,B_632] :
      ( r1_tarski(A_629,k1_tops_1(A_630,C_631))
      | ~ r1_tarski(A_629,k1_tops_1(A_630,B_632))
      | ~ r1_tarski(B_632,C_631)
      | ~ m1_subset_1(C_631,k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ m1_subset_1(B_632,k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ l1_pre_topc(A_630) ) ),
    inference(resolution,[status(thm)],[c_19960,c_8])).

tff(c_95773,plain,(
    ! [A_1242,B_1243,C_1244,C_1245] :
      ( r1_tarski(k1_tops_1(A_1242,B_1243),k1_tops_1(A_1242,C_1244))
      | ~ r1_tarski(C_1245,C_1244)
      | ~ m1_subset_1(C_1244,k1_zfmisc_1(u1_struct_0(A_1242)))
      | ~ r1_tarski(B_1243,C_1245)
      | ~ m1_subset_1(C_1245,k1_zfmisc_1(u1_struct_0(A_1242)))
      | ~ m1_subset_1(B_1243,k1_zfmisc_1(u1_struct_0(A_1242)))
      | ~ l1_pre_topc(A_1242) ) ),
    inference(resolution,[status(thm)],[c_54,c_28184])).

tff(c_193516,plain,(
    ! [A_1683,B_1684] :
      ( r1_tarski(k1_tops_1(A_1683,B_1684),k1_tops_1(A_1683,k2_pre_topc('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_1683)))
      | ~ r1_tarski(B_1684,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_1683)))
      | ~ m1_subset_1(B_1684,k1_zfmisc_1(u1_struct_0(A_1683)))
      | ~ l1_pre_topc(A_1683) ) ),
    inference(resolution,[status(thm)],[c_682,c_95773])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_20] :
      ( r1_tarski(k3_subset_1(A_20,k2_subset_1(A_20)),k2_subset_1(A_20))
      | ~ m1_subset_1(k2_subset_1(A_20),k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [A_20] : r1_tarski(k3_subset_1(A_20,k2_subset_1(A_20)),k2_subset_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_915,plain,(
    ! [A_20] : r1_tarski(k3_subset_1(A_20,A_20),A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_891,c_68])).

tff(c_918,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_10])).

tff(c_18496,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18464,c_26])).

tff(c_19190,plain,(
    ! [A_470,C_471,B_472] :
      ( r1_tarski(k3_subset_1(A_470,C_471),B_472)
      | ~ r1_tarski(k3_subset_1(A_470,B_472),C_471)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(A_470))
      | ~ m1_subset_1(B_472,k1_zfmisc_1(A_470)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_19199,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18496,c_19190])).

tff(c_19239,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_918,c_19199])).

tff(c_19221,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k3_subset_1(A_77,A_77),B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_174,c_19190])).

tff(c_19277,plain,(
    ! [A_473,B_474] :
      ( r1_tarski(k3_subset_1(A_473,A_473),B_474)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(A_473)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_19221])).

tff(c_87,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,(
    ! [A_6] : r1_tarski(k2_subset_1(A_6),A_6) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_138,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(A_72,C_73)
      | ~ r1_tarski(B_74,C_73)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [A_75,A_76] :
      ( r1_tarski(A_75,A_76)
      | ~ r1_tarski(A_75,k2_subset_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_94,c_138])).

tff(c_188,plain,(
    ! [A_80] : r1_tarski(k3_subset_1(A_80,k2_subset_1(A_80)),A_80) ),
    inference(resolution,[status(thm)],[c_68,c_151])).

tff(c_198,plain,(
    ! [A_3,A_80] :
      ( r1_tarski(A_3,A_80)
      | ~ r1_tarski(A_3,k3_subset_1(A_80,k2_subset_1(A_80))) ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_903,plain,(
    ! [A_3,A_80] :
      ( r1_tarski(A_3,A_80)
      | ~ r1_tarski(A_3,k3_subset_1(A_80,A_80)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_198])).

tff(c_19413,plain,(
    ! [A_476,A_477] :
      ( r1_tarski(k3_subset_1(A_476,A_476),A_477)
      | ~ m1_subset_1(k3_subset_1(A_477,A_477),k1_zfmisc_1(A_476)) ) ),
    inference(resolution,[status(thm)],[c_19277,c_903])).

tff(c_19429,plain,(
    ! [B_478,A_479] :
      ( r1_tarski(k3_subset_1(B_478,B_478),A_479)
      | ~ r1_tarski(k3_subset_1(A_479,A_479),B_478) ) ),
    inference(resolution,[status(thm)],[c_28,c_19413])).

tff(c_19463,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_19239,c_19429])).

tff(c_19757,plain,(
    ! [A_485] :
      ( r1_tarski(A_485,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_485,k3_subset_1('#skF_2','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_19463,c_8])).

tff(c_19797,plain,(
    r1_tarski(k3_subset_1(k3_subset_1('#skF_2','#skF_2'),k3_subset_1('#skF_2','#skF_2')),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_915,c_19757])).

tff(c_19428,plain,(
    ! [B_23,A_477] :
      ( r1_tarski(k3_subset_1(B_23,B_23),A_477)
      | ~ r1_tarski(k3_subset_1(A_477,A_477),B_23) ) ),
    inference(resolution,[status(thm)],[c_28,c_19413])).

tff(c_20038,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')),k3_subset_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_19797,c_19428])).

tff(c_723,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k1_tops_1(A_110,B_111),B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_731,plain,(
    ! [B_111] :
      ( r1_tarski(k1_tops_1('#skF_1',B_111),B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_723])).

tff(c_742,plain,(
    ! [B_112] :
      ( r1_tarski(k1_tops_1('#skF_1',B_112),B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_731])).

tff(c_756,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_742])).

tff(c_95,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_102,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_95])).

tff(c_212,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_82,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_102,c_138])).

tff(c_1346,plain,(
    ! [A_142,A_143] :
      ( r1_tarski(A_142,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_142,A_143)
      | ~ r1_tarski(A_143,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_212,c_8])).

tff(c_1390,plain,(
    ! [A_20] :
      ( r1_tarski(k3_subset_1(A_20,A_20),k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_915,c_1346])).

tff(c_19466,plain,(
    ! [A_20] :
      ( r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')),A_20)
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1390,c_19429])).

tff(c_19256,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k3_subset_1(A_77,A_77),B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_19221])).

tff(c_19596,plain,(
    ! [B_482,A_483] :
      ( r1_tarski(k3_subset_1(B_482,B_482),A_483)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(A_483)) ) ),
    inference(resolution,[status(thm)],[c_19256,c_19429])).

tff(c_762,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,'#skF_2')
      | ~ r1_tarski(A_3,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_756,c_8])).

tff(c_20867,plain,(
    ! [B_504] :
      ( r1_tarski(k3_subset_1(B_504,B_504),'#skF_2')
      | ~ m1_subset_1(B_504,k1_zfmisc_1(k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_19596,c_762])).

tff(c_20881,plain,(
    ! [A_505] :
      ( r1_tarski(k3_subset_1(A_505,A_505),'#skF_2')
      | ~ r1_tarski(A_505,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_20867])).

tff(c_20913,plain,(
    ! [A_506] :
      ( r1_tarski(k3_subset_1('#skF_2','#skF_2'),A_506)
      | ~ r1_tarski(A_506,k1_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_20881,c_19428])).

tff(c_20924,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_2'),k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_19466,c_20913])).

tff(c_20962,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_2'),k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_20924])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21025,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1('#skF_2','#skF_2')
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')),k3_subset_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20962,c_2])).

tff(c_21046,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20038,c_21025])).

tff(c_21128,plain,
    ( m1_subset_1(k3_subset_1('#skF_2','#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_21046,c_12])).

tff(c_21159,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_21128])).

tff(c_1413,plain,(
    ! [B_144,A_145] :
      ( v1_tops_1(B_144,A_145)
      | k2_pre_topc(A_145,B_144) != k2_struct_0(A_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1431,plain,(
    ! [B_144] :
      ( v1_tops_1(B_144,'#skF_1')
      | k2_pre_topc('#skF_1',B_144) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1413])).

tff(c_1487,plain,(
    ! [B_148] :
      ( v1_tops_1(B_148,'#skF_1')
      | k2_pre_topc('#skF_1',B_148) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1431])).

tff(c_1507,plain,
    ( v1_tops_1(k2_struct_0('#skF_1'),'#skF_1')
    | k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_918,c_1487])).

tff(c_1513,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1507])).

tff(c_1010,plain,(
    ! [B_122] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_122),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_998])).

tff(c_1019,plain,(
    ! [B_123] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_123),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_1010])).

tff(c_1032,plain,(
    ! [B_123] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_123),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1019,c_26])).

tff(c_2161,plain,(
    ! [A_173,A_174] :
      ( r1_tarski(A_173,k2_pre_topc(A_174,A_173))
      | ~ l1_pre_topc(A_174)
      | ~ r1_tarski(A_173,u1_struct_0(A_174)) ) ),
    inference(resolution,[status(thm)],[c_28,c_533])).

tff(c_18346,plain,(
    ! [A_439,A_440] :
      ( k2_pre_topc(A_439,A_440) = A_440
      | ~ r1_tarski(k2_pre_topc(A_439,A_440),A_440)
      | ~ l1_pre_topc(A_439)
      | ~ r1_tarski(A_440,u1_struct_0(A_439)) ) ),
    inference(resolution,[status(thm)],[c_2161,c_2])).

tff(c_18394,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k2_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1032,c_18346])).

tff(c_18424,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_6,c_101,c_66,c_18394])).

tff(c_18426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1513,c_18424])).

tff(c_18427,plain,(
    v1_tops_1(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1507])).

tff(c_316,plain,(
    ! [B_23,A_22] :
      ( k3_subset_1(B_23,k3_subset_1(B_23,A_22)) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_28,c_306])).

tff(c_21122,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1('#skF_2','#skF_2')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21046,c_316])).

tff(c_21155,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1('#skF_2','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_21122])).

tff(c_18676,plain,(
    ! [B_448,A_449] :
      ( v2_tops_1(B_448,A_449)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_449),B_448),A_449)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0(A_449)))
      | ~ l1_pre_topc(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18691,plain,(
    ! [B_448] :
      ( v2_tops_1(B_448,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_448),'#skF_1')
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_18676])).

tff(c_18693,plain,(
    ! [B_448] :
      ( v2_tops_1(B_448,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_448),'#skF_1')
      | ~ m1_subset_1(B_448,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_18691])).

tff(c_21418,plain,
    ( v2_tops_1(k3_subset_1('#skF_2','#skF_2'),'#skF_1')
    | ~ v1_tops_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_21155,c_18693])).

tff(c_21441,plain,(
    v2_tops_1(k3_subset_1('#skF_2','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21159,c_18427,c_21418])).

tff(c_148,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_72,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_102,c_138])).

tff(c_1208,plain,(
    ! [B_134] :
      ( k1_tops_1('#skF_1',B_134) = k1_xboole_0
      | ~ v2_tops_1(B_134,'#skF_1')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1190])).

tff(c_1227,plain,(
    ! [B_136] :
      ( k1_tops_1('#skF_1',B_136) = k1_xboole_0
      | ~ v2_tops_1(B_136,'#skF_1')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1208])).

tff(c_18992,plain,(
    ! [A_463] :
      ( k1_tops_1('#skF_1',A_463) = k1_xboole_0
      | ~ v2_tops_1(A_463,'#skF_1')
      | ~ r1_tarski(A_463,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_1227])).

tff(c_19066,plain,(
    ! [A_72] :
      ( k1_tops_1('#skF_1',A_72) = k1_xboole_0
      | ~ v2_tops_1(A_72,'#skF_1')
      | ~ r1_tarski(A_72,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_148,c_18992])).

tff(c_21451,plain,
    ( k1_tops_1('#skF_1',k3_subset_1('#skF_2','#skF_2')) = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_21441,c_19066])).

tff(c_21454,plain,(
    k1_tops_1('#skF_1',k3_subset_1('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_21451])).

tff(c_755,plain,(
    ! [A_22] :
      ( r1_tarski(k1_tops_1('#skF_1',A_22),A_22)
      | ~ r1_tarski(A_22,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_742])).

tff(c_983,plain,(
    ! [A_120] : r1_tarski(k3_subset_1(A_120,A_120),A_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_891,c_68])).

tff(c_992,plain,(
    r1_tarski(k3_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_983,c_762])).

tff(c_19467,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_992,c_19429])).

tff(c_19909,plain,(
    ! [A_487] :
      ( r1_tarski(A_487,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_487,k3_subset_1('#skF_2','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_19467,c_8])).

tff(c_19933,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k3_subset_1('#skF_2','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_755,c_19909])).

tff(c_19955,plain,(
    r1_tarski(k1_tops_1('#skF_1',k3_subset_1('#skF_2','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19463,c_19933])).

tff(c_21462,plain,(
    r1_tarski(k1_xboole_0,k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21454,c_19955])).

tff(c_23748,plain,(
    ! [A_545] :
      ( r1_tarski(A_545,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_545,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_21462,c_8])).

tff(c_23811,plain,(
    ! [A_545] :
      ( k1_tops_1('#skF_1','#skF_2') = A_545
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),A_545)
      | ~ r1_tarski(A_545,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_23748,c_2])).

tff(c_193538,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_193516,c_23811])).

tff(c_193631,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_104,c_101,c_6,c_69046,c_101,c_6,c_23544,c_23544,c_193538])).

tff(c_193633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1170,c_193631])).

tff(c_193634,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1169])).

tff(c_194131,plain,(
    ! [A_1709,B_1710] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_1709),B_1710),A_1709)
      | ~ v2_tops_1(B_1710,A_1709)
      | ~ m1_subset_1(B_1710,k1_zfmisc_1(u1_struct_0(A_1709)))
      | ~ l1_pre_topc(A_1709) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_194146,plain,(
    ! [B_1710] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_1710),'#skF_1')
      | ~ v2_tops_1(B_1710,'#skF_1')
      | ~ m1_subset_1(B_1710,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_194131])).

tff(c_194157,plain,(
    ! [B_1711] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_1711),'#skF_1')
      | ~ v2_tops_1(B_1711,'#skF_1')
      | ~ m1_subset_1(B_1711,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_194146])).

tff(c_60,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_103,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_60])).

tff(c_194160,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_194157,c_103])).

tff(c_194179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_193634,c_194160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.03/42.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.03/42.36  
% 52.03/42.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.03/42.36  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 52.03/42.36  
% 52.03/42.36  %Foreground sorts:
% 52.03/42.36  
% 52.03/42.36  
% 52.03/42.36  %Background operators:
% 52.03/42.36  
% 52.03/42.36  
% 52.03/42.36  %Foreground operators:
% 52.03/42.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.03/42.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 52.03/42.36  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 52.03/42.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 52.03/42.36  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 52.03/42.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 52.03/42.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 52.03/42.36  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 52.03/42.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 52.03/42.36  tff('#skF_2', type, '#skF_2': $i).
% 52.03/42.36  tff('#skF_1', type, '#skF_1': $i).
% 52.03/42.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 52.03/42.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 52.03/42.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.03/42.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.03/42.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 52.03/42.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 52.03/42.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 52.03/42.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 52.03/42.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 52.03/42.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 52.03/42.36  
% 52.03/42.39  tff(f_170, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 52.03/42.39  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 52.03/42.39  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 52.03/42.39  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 52.03/42.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 52.03/42.39  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 52.03/42.39  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 52.03/42.39  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 52.03/42.39  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 52.03/42.39  tff(f_87, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 52.03/42.39  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 52.03/42.39  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 52.03/42.39  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 52.03/42.39  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 52.03/42.39  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 52.03/42.39  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 52.03/42.39  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 52.03/42.39  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 52.03/42.39  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 52.03/42.39  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 52.03/42.39  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 52.03/42.39  tff(c_34, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 52.03/42.39  tff(c_82, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_81])).
% 52.03/42.39  tff(c_97, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_34, c_82])).
% 52.03/42.39  tff(c_101, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_97])).
% 52.03/42.39  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 52.03/42.39  tff(c_104, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_64])).
% 52.03/42.39  tff(c_1087, plain, (![B_125, A_126]: (v2_tops_1(B_125, A_126) | k1_tops_1(A_126, B_125)!=k1_xboole_0 | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_160])).
% 52.03/42.39  tff(c_1105, plain, (![B_125]: (v2_tops_1(B_125, '#skF_1') | k1_tops_1('#skF_1', B_125)!=k1_xboole_0 | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1087])).
% 52.03/42.39  tff(c_1146, plain, (![B_130]: (v2_tops_1(B_130, '#skF_1') | k1_tops_1('#skF_1', B_130)!=k1_xboole_0 | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1105])).
% 52.03/42.39  tff(c_1169, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_1146])).
% 52.03/42.39  tff(c_1170, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1169])).
% 52.03/42.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 52.03/42.39  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 52.03/42.39  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 52.03/42.39  tff(c_167, plain, (![A_77, B_78]: (m1_subset_1(k3_subset_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 52.03/42.39  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 52.03/42.39  tff(c_174, plain, (![A_77, B_78]: (r1_tarski(k3_subset_1(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_167, c_26])).
% 52.03/42.39  tff(c_849, plain, (![A_114, B_115]: (k2_subset_1(A_114)=B_115 | ~r1_tarski(k3_subset_1(A_114, B_115), B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 52.03/42.39  tff(c_884, plain, (![A_116]: (k2_subset_1(A_116)=A_116 | ~m1_subset_1(A_116, k1_zfmisc_1(A_116)))), inference(resolution, [status(thm)], [c_174, c_849])).
% 52.03/42.39  tff(c_888, plain, (![B_23]: (k2_subset_1(B_23)=B_23 | ~r1_tarski(B_23, B_23))), inference(resolution, [status(thm)], [c_28, c_884])).
% 52.03/42.39  tff(c_891, plain, (![B_23]: (k2_subset_1(B_23)=B_23)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_888])).
% 52.03/42.39  tff(c_306, plain, (![A_88, B_89]: (k3_subset_1(A_88, k3_subset_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 52.03/42.39  tff(c_317, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_104, c_306])).
% 52.03/42.39  tff(c_863, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_subset_1(k2_struct_0('#skF_1')) | ~r1_tarski('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_317, c_849])).
% 52.03/42.39  tff(c_18451, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1') | ~r1_tarski('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_891, c_863])).
% 52.03/42.39  tff(c_18452, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_18451])).
% 52.03/42.39  tff(c_18455, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_18452])).
% 52.03/42.39  tff(c_18462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_18455])).
% 52.03/42.39  tff(c_18464, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_18451])).
% 52.03/42.39  tff(c_32, plain, (![A_25, B_26]: (m1_subset_1(k2_pre_topc(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 52.03/42.39  tff(c_19480, plain, (![A_480, B_481]: (k3_subset_1(u1_struct_0(A_480), k2_pre_topc(A_480, k3_subset_1(u1_struct_0(A_480), B_481)))=k1_tops_1(A_480, B_481) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0(A_480))) | ~l1_pre_topc(A_480))), inference(cnfTransformation, [status(thm)], [f_105])).
% 52.03/42.39  tff(c_27768, plain, (![A_621, B_622]: (m1_subset_1(k1_tops_1(A_621, B_622), k1_zfmisc_1(u1_struct_0(A_621))) | ~m1_subset_1(k2_pre_topc(A_621, k3_subset_1(u1_struct_0(A_621), B_622)), k1_zfmisc_1(u1_struct_0(A_621))) | ~m1_subset_1(B_622, k1_zfmisc_1(u1_struct_0(A_621))) | ~l1_pre_topc(A_621))), inference(superposition, [status(thm), theory('equality')], [c_19480, c_12])).
% 52.03/42.39  tff(c_57915, plain, (![A_960, B_961]: (m1_subset_1(k1_tops_1(A_960, B_961), k1_zfmisc_1(u1_struct_0(A_960))) | ~m1_subset_1(B_961, k1_zfmisc_1(u1_struct_0(A_960))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_960), B_961), k1_zfmisc_1(u1_struct_0(A_960))) | ~l1_pre_topc(A_960))), inference(resolution, [status(thm)], [c_32, c_27768])).
% 52.03/42.39  tff(c_57950, plain, (![B_961]: (m1_subset_1(k1_tops_1('#skF_1', B_961), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_961, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), B_961), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_57915])).
% 52.03/42.39  tff(c_58221, plain, (![B_963]: (m1_subset_1(k1_tops_1('#skF_1', B_963), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_963, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_963), k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_101, c_101, c_57950])).
% 52.03/42.39  tff(c_58264, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_317, c_58221])).
% 52.03/42.39  tff(c_58285, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_18464, c_58264])).
% 52.03/42.39  tff(c_19532, plain, (![B_481]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_481)))=k1_tops_1('#skF_1', B_481) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_19480])).
% 52.03/42.39  tff(c_19671, plain, (![B_484]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_484)))=k1_tops_1('#skF_1', B_484) | ~m1_subset_1(B_484, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_101, c_19532])).
% 52.03/42.39  tff(c_19720, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_317, c_19671])).
% 52.03/42.39  tff(c_19726, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18464, c_19720])).
% 52.03/42.39  tff(c_998, plain, (![A_121, B_122]: (m1_subset_1(k2_pre_topc(A_121, B_122), k1_zfmisc_1(u1_struct_0(A_121))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_87])).
% 52.03/42.39  tff(c_14, plain, (![A_9, B_10]: (k3_subset_1(A_9, k3_subset_1(A_9, B_10))=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 52.03/42.39  tff(c_25014, plain, (![A_570, B_571]: (k3_subset_1(u1_struct_0(A_570), k3_subset_1(u1_struct_0(A_570), k2_pre_topc(A_570, B_571)))=k2_pre_topc(A_570, B_571) | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0(A_570))) | ~l1_pre_topc(A_570))), inference(resolution, [status(thm)], [c_998, c_14])).
% 52.03/42.39  tff(c_25093, plain, (![B_571]: (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_571)))=k2_pre_topc('#skF_1', B_571) | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_25014])).
% 52.03/42.39  tff(c_25110, plain, (![B_571]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_571)))=k2_pre_topc('#skF_1', B_571) | ~m1_subset_1(B_571, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_101, c_25093])).
% 52.03/42.39  tff(c_36901, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_19726, c_25110])).
% 52.03/42.39  tff(c_36965, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_36901])).
% 52.03/42.39  tff(c_68955, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_36965, c_12])).
% 52.03/42.39  tff(c_69046, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58285, c_68955])).
% 52.03/42.39  tff(c_62, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 52.03/42.39  tff(c_1290, plain, (![A_139, B_140]: (v2_tops_1(k2_pre_topc(A_139, B_140), A_139) | ~v3_tops_1(B_140, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_132])).
% 52.03/42.39  tff(c_1303, plain, (![B_140]: (v2_tops_1(k2_pre_topc('#skF_1', B_140), '#skF_1') | ~v3_tops_1(B_140, '#skF_1') | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1290])).
% 52.03/42.39  tff(c_1318, plain, (![B_141]: (v2_tops_1(k2_pre_topc('#skF_1', B_141), '#skF_1') | ~v3_tops_1(B_141, '#skF_1') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1303])).
% 52.03/42.39  tff(c_1336, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_104, c_1318])).
% 52.03/42.40  tff(c_1343, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1336])).
% 52.03/42.40  tff(c_1190, plain, (![A_133, B_134]: (k1_tops_1(A_133, B_134)=k1_xboole_0 | ~v2_tops_1(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_160])).
% 52.03/42.40  tff(c_23525, plain, (![A_540, B_541]: (k1_tops_1(A_540, k2_pre_topc(A_540, B_541))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_540, B_541), A_540) | ~m1_subset_1(B_541, k1_zfmisc_1(u1_struct_0(A_540))) | ~l1_pre_topc(A_540))), inference(resolution, [status(thm)], [c_32, c_1190])).
% 52.03/42.40  tff(c_23534, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1343, c_23525])).
% 52.03/42.40  tff(c_23544, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_104, c_101, c_23534])).
% 52.03/42.40  tff(c_533, plain, (![B_101, A_102]: (r1_tarski(B_101, k2_pre_topc(A_102, B_101)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_98])).
% 52.03/42.40  tff(c_541, plain, (![B_101]: (r1_tarski(B_101, k2_pre_topc('#skF_1', B_101)) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_533])).
% 52.03/42.40  tff(c_668, plain, (![B_107]: (r1_tarski(B_107, k2_pre_topc('#skF_1', B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_541])).
% 52.03/42.40  tff(c_682, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_104, c_668])).
% 52.03/42.40  tff(c_54, plain, (![A_46, B_50, C_52]: (r1_tarski(k1_tops_1(A_46, B_50), k1_tops_1(A_46, C_52)) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_151])).
% 52.03/42.40  tff(c_19960, plain, (![A_488, B_489, C_490]: (r1_tarski(k1_tops_1(A_488, B_489), k1_tops_1(A_488, C_490)) | ~r1_tarski(B_489, C_490) | ~m1_subset_1(C_490, k1_zfmisc_1(u1_struct_0(A_488))) | ~m1_subset_1(B_489, k1_zfmisc_1(u1_struct_0(A_488))) | ~l1_pre_topc(A_488))), inference(cnfTransformation, [status(thm)], [f_151])).
% 52.03/42.40  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 52.03/42.40  tff(c_28184, plain, (![A_629, A_630, C_631, B_632]: (r1_tarski(A_629, k1_tops_1(A_630, C_631)) | ~r1_tarski(A_629, k1_tops_1(A_630, B_632)) | ~r1_tarski(B_632, C_631) | ~m1_subset_1(C_631, k1_zfmisc_1(u1_struct_0(A_630))) | ~m1_subset_1(B_632, k1_zfmisc_1(u1_struct_0(A_630))) | ~l1_pre_topc(A_630))), inference(resolution, [status(thm)], [c_19960, c_8])).
% 52.03/42.40  tff(c_95773, plain, (![A_1242, B_1243, C_1244, C_1245]: (r1_tarski(k1_tops_1(A_1242, B_1243), k1_tops_1(A_1242, C_1244)) | ~r1_tarski(C_1245, C_1244) | ~m1_subset_1(C_1244, k1_zfmisc_1(u1_struct_0(A_1242))) | ~r1_tarski(B_1243, C_1245) | ~m1_subset_1(C_1245, k1_zfmisc_1(u1_struct_0(A_1242))) | ~m1_subset_1(B_1243, k1_zfmisc_1(u1_struct_0(A_1242))) | ~l1_pre_topc(A_1242))), inference(resolution, [status(thm)], [c_54, c_28184])).
% 52.03/42.40  tff(c_193516, plain, (![A_1683, B_1684]: (r1_tarski(k1_tops_1(A_1683, B_1684), k1_tops_1(A_1683, k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0(A_1683))) | ~r1_tarski(B_1684, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_1683))) | ~m1_subset_1(B_1684, k1_zfmisc_1(u1_struct_0(A_1683))) | ~l1_pre_topc(A_1683))), inference(resolution, [status(thm)], [c_682, c_95773])).
% 52.03/42.40  tff(c_10, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 52.03/42.40  tff(c_22, plain, (![A_20]: (r1_tarski(k3_subset_1(A_20, k2_subset_1(A_20)), k2_subset_1(A_20)) | ~m1_subset_1(k2_subset_1(A_20), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 52.03/42.40  tff(c_68, plain, (![A_20]: (r1_tarski(k3_subset_1(A_20, k2_subset_1(A_20)), k2_subset_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 52.03/42.40  tff(c_915, plain, (![A_20]: (r1_tarski(k3_subset_1(A_20, A_20), A_20))), inference(demodulation, [status(thm), theory('equality')], [c_891, c_891, c_68])).
% 52.03/42.40  tff(c_918, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_891, c_10])).
% 52.03/42.40  tff(c_18496, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18464, c_26])).
% 52.03/42.40  tff(c_19190, plain, (![A_470, C_471, B_472]: (r1_tarski(k3_subset_1(A_470, C_471), B_472) | ~r1_tarski(k3_subset_1(A_470, B_472), C_471) | ~m1_subset_1(C_471, k1_zfmisc_1(A_470)) | ~m1_subset_1(B_472, k1_zfmisc_1(A_470)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 52.03/42.40  tff(c_19199, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18496, c_19190])).
% 52.03/42.40  tff(c_19239, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_918, c_19199])).
% 52.03/42.40  tff(c_19221, plain, (![A_77, B_78]: (r1_tarski(k3_subset_1(A_77, A_77), B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_174, c_19190])).
% 52.03/42.40  tff(c_19277, plain, (![A_473, B_474]: (r1_tarski(k3_subset_1(A_473, A_473), B_474) | ~m1_subset_1(B_474, k1_zfmisc_1(A_473)))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_19221])).
% 52.03/42.40  tff(c_87, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 52.03/42.40  tff(c_94, plain, (![A_6]: (r1_tarski(k2_subset_1(A_6), A_6))), inference(resolution, [status(thm)], [c_10, c_87])).
% 52.03/42.40  tff(c_138, plain, (![A_72, C_73, B_74]: (r1_tarski(A_72, C_73) | ~r1_tarski(B_74, C_73) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 52.03/42.40  tff(c_151, plain, (![A_75, A_76]: (r1_tarski(A_75, A_76) | ~r1_tarski(A_75, k2_subset_1(A_76)))), inference(resolution, [status(thm)], [c_94, c_138])).
% 52.03/42.40  tff(c_188, plain, (![A_80]: (r1_tarski(k3_subset_1(A_80, k2_subset_1(A_80)), A_80))), inference(resolution, [status(thm)], [c_68, c_151])).
% 52.03/42.40  tff(c_198, plain, (![A_3, A_80]: (r1_tarski(A_3, A_80) | ~r1_tarski(A_3, k3_subset_1(A_80, k2_subset_1(A_80))))), inference(resolution, [status(thm)], [c_188, c_8])).
% 52.03/42.40  tff(c_903, plain, (![A_3, A_80]: (r1_tarski(A_3, A_80) | ~r1_tarski(A_3, k3_subset_1(A_80, A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_891, c_198])).
% 52.03/42.40  tff(c_19413, plain, (![A_476, A_477]: (r1_tarski(k3_subset_1(A_476, A_476), A_477) | ~m1_subset_1(k3_subset_1(A_477, A_477), k1_zfmisc_1(A_476)))), inference(resolution, [status(thm)], [c_19277, c_903])).
% 52.03/42.40  tff(c_19429, plain, (![B_478, A_479]: (r1_tarski(k3_subset_1(B_478, B_478), A_479) | ~r1_tarski(k3_subset_1(A_479, A_479), B_478))), inference(resolution, [status(thm)], [c_28, c_19413])).
% 52.03/42.40  tff(c_19463, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_19239, c_19429])).
% 52.03/42.40  tff(c_19757, plain, (![A_485]: (r1_tarski(A_485, k2_struct_0('#skF_1')) | ~r1_tarski(A_485, k3_subset_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_19463, c_8])).
% 52.03/42.40  tff(c_19797, plain, (r1_tarski(k3_subset_1(k3_subset_1('#skF_2', '#skF_2'), k3_subset_1('#skF_2', '#skF_2')), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_915, c_19757])).
% 52.03/42.40  tff(c_19428, plain, (![B_23, A_477]: (r1_tarski(k3_subset_1(B_23, B_23), A_477) | ~r1_tarski(k3_subset_1(A_477, A_477), B_23))), inference(resolution, [status(thm)], [c_28, c_19413])).
% 52.03/42.40  tff(c_20038, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')), k3_subset_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_19797, c_19428])).
% 52.03/42.40  tff(c_723, plain, (![A_110, B_111]: (r1_tarski(k1_tops_1(A_110, B_111), B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_139])).
% 52.03/42.40  tff(c_731, plain, (![B_111]: (r1_tarski(k1_tops_1('#skF_1', B_111), B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_723])).
% 52.03/42.40  tff(c_742, plain, (![B_112]: (r1_tarski(k1_tops_1('#skF_1', B_112), B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_731])).
% 52.03/42.40  tff(c_756, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_104, c_742])).
% 52.03/42.40  tff(c_95, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_87])).
% 52.03/42.40  tff(c_102, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_95])).
% 52.03/42.40  tff(c_212, plain, (![A_82]: (r1_tarski(A_82, k2_struct_0('#skF_1')) | ~r1_tarski(A_82, '#skF_2'))), inference(resolution, [status(thm)], [c_102, c_138])).
% 52.03/42.40  tff(c_1346, plain, (![A_142, A_143]: (r1_tarski(A_142, k2_struct_0('#skF_1')) | ~r1_tarski(A_142, A_143) | ~r1_tarski(A_143, '#skF_2'))), inference(resolution, [status(thm)], [c_212, c_8])).
% 52.03/42.40  tff(c_1390, plain, (![A_20]: (r1_tarski(k3_subset_1(A_20, A_20), k2_struct_0('#skF_1')) | ~r1_tarski(A_20, '#skF_2'))), inference(resolution, [status(thm)], [c_915, c_1346])).
% 52.03/42.40  tff(c_19466, plain, (![A_20]: (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')), A_20) | ~r1_tarski(A_20, '#skF_2'))), inference(resolution, [status(thm)], [c_1390, c_19429])).
% 52.03/42.40  tff(c_19256, plain, (![A_77, B_78]: (r1_tarski(k3_subset_1(A_77, A_77), B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_19221])).
% 52.03/42.40  tff(c_19596, plain, (![B_482, A_483]: (r1_tarski(k3_subset_1(B_482, B_482), A_483) | ~m1_subset_1(B_482, k1_zfmisc_1(A_483)))), inference(resolution, [status(thm)], [c_19256, c_19429])).
% 52.03/42.40  tff(c_762, plain, (![A_3]: (r1_tarski(A_3, '#skF_2') | ~r1_tarski(A_3, k1_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_756, c_8])).
% 52.03/42.40  tff(c_20867, plain, (![B_504]: (r1_tarski(k3_subset_1(B_504, B_504), '#skF_2') | ~m1_subset_1(B_504, k1_zfmisc_1(k1_tops_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_19596, c_762])).
% 52.03/42.40  tff(c_20881, plain, (![A_505]: (r1_tarski(k3_subset_1(A_505, A_505), '#skF_2') | ~r1_tarski(A_505, k1_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_28, c_20867])).
% 52.03/42.40  tff(c_20913, plain, (![A_506]: (r1_tarski(k3_subset_1('#skF_2', '#skF_2'), A_506) | ~r1_tarski(A_506, k1_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_20881, c_19428])).
% 52.03/42.40  tff(c_20924, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_2'), k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_19466, c_20913])).
% 52.03/42.40  tff(c_20962, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_2'), k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_756, c_20924])).
% 52.03/42.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 52.03/42.40  tff(c_21025, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k3_subset_1('#skF_2', '#skF_2') | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')), k3_subset_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_20962, c_2])).
% 52.03/42.40  tff(c_21046, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k3_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20038, c_21025])).
% 52.03/42.40  tff(c_21128, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_21046, c_12])).
% 52.03/42.40  tff(c_21159, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_21128])).
% 52.03/42.40  tff(c_1413, plain, (![B_144, A_145]: (v1_tops_1(B_144, A_145) | k2_pre_topc(A_145, B_144)!=k2_struct_0(A_145) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_114])).
% 52.03/42.40  tff(c_1431, plain, (![B_144]: (v1_tops_1(B_144, '#skF_1') | k2_pre_topc('#skF_1', B_144)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_144, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1413])).
% 52.03/42.40  tff(c_1487, plain, (![B_148]: (v1_tops_1(B_148, '#skF_1') | k2_pre_topc('#skF_1', B_148)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_148, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1431])).
% 52.03/42.40  tff(c_1507, plain, (v1_tops_1(k2_struct_0('#skF_1'), '#skF_1') | k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_918, c_1487])).
% 52.03/42.40  tff(c_1513, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1507])).
% 52.03/42.40  tff(c_1010, plain, (![B_122]: (m1_subset_1(k2_pre_topc('#skF_1', B_122), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_998])).
% 52.03/42.40  tff(c_1019, plain, (![B_123]: (m1_subset_1(k2_pre_topc('#skF_1', B_123), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_1010])).
% 52.03/42.40  tff(c_1032, plain, (![B_123]: (r1_tarski(k2_pre_topc('#skF_1', B_123), k2_struct_0('#skF_1')) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1019, c_26])).
% 52.03/42.40  tff(c_2161, plain, (![A_173, A_174]: (r1_tarski(A_173, k2_pre_topc(A_174, A_173)) | ~l1_pre_topc(A_174) | ~r1_tarski(A_173, u1_struct_0(A_174)))), inference(resolution, [status(thm)], [c_28, c_533])).
% 52.03/42.40  tff(c_18346, plain, (![A_439, A_440]: (k2_pre_topc(A_439, A_440)=A_440 | ~r1_tarski(k2_pre_topc(A_439, A_440), A_440) | ~l1_pre_topc(A_439) | ~r1_tarski(A_440, u1_struct_0(A_439)))), inference(resolution, [status(thm)], [c_2161, c_2])).
% 52.03/42.40  tff(c_18394, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1032, c_18346])).
% 52.03/42.40  tff(c_18424, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_6, c_101, c_66, c_18394])).
% 52.03/42.40  tff(c_18426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1513, c_18424])).
% 52.03/42.40  tff(c_18427, plain, (v1_tops_1(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_1507])).
% 52.03/42.40  tff(c_316, plain, (![B_23, A_22]: (k3_subset_1(B_23, k3_subset_1(B_23, A_22))=A_22 | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_28, c_306])).
% 52.03/42.40  tff(c_21122, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_21046, c_316])).
% 52.03/42.40  tff(c_21155, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_21122])).
% 52.03/42.40  tff(c_18676, plain, (![B_448, A_449]: (v2_tops_1(B_448, A_449) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_449), B_448), A_449) | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0(A_449))) | ~l1_pre_topc(A_449))), inference(cnfTransformation, [status(thm)], [f_123])).
% 52.03/42.40  tff(c_18691, plain, (![B_448]: (v2_tops_1(B_448, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_448), '#skF_1') | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_18676])).
% 52.03/42.40  tff(c_18693, plain, (![B_448]: (v2_tops_1(B_448, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_448), '#skF_1') | ~m1_subset_1(B_448, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_18691])).
% 52.03/42.40  tff(c_21418, plain, (v2_tops_1(k3_subset_1('#skF_2', '#skF_2'), '#skF_1') | ~v1_tops_1(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_21155, c_18693])).
% 52.03/42.40  tff(c_21441, plain, (v2_tops_1(k3_subset_1('#skF_2', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21159, c_18427, c_21418])).
% 52.03/42.40  tff(c_148, plain, (![A_72]: (r1_tarski(A_72, k2_struct_0('#skF_1')) | ~r1_tarski(A_72, '#skF_2'))), inference(resolution, [status(thm)], [c_102, c_138])).
% 52.03/42.40  tff(c_1208, plain, (![B_134]: (k1_tops_1('#skF_1', B_134)=k1_xboole_0 | ~v2_tops_1(B_134, '#skF_1') | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1190])).
% 52.03/42.40  tff(c_1227, plain, (![B_136]: (k1_tops_1('#skF_1', B_136)=k1_xboole_0 | ~v2_tops_1(B_136, '#skF_1') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1208])).
% 52.03/42.40  tff(c_18992, plain, (![A_463]: (k1_tops_1('#skF_1', A_463)=k1_xboole_0 | ~v2_tops_1(A_463, '#skF_1') | ~r1_tarski(A_463, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_1227])).
% 52.03/42.40  tff(c_19066, plain, (![A_72]: (k1_tops_1('#skF_1', A_72)=k1_xboole_0 | ~v2_tops_1(A_72, '#skF_1') | ~r1_tarski(A_72, '#skF_2'))), inference(resolution, [status(thm)], [c_148, c_18992])).
% 52.03/42.40  tff(c_21451, plain, (k1_tops_1('#skF_1', k3_subset_1('#skF_2', '#skF_2'))=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_2', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_21441, c_19066])).
% 52.03/42.40  tff(c_21454, plain, (k1_tops_1('#skF_1', k3_subset_1('#skF_2', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_915, c_21451])).
% 52.03/42.40  tff(c_755, plain, (![A_22]: (r1_tarski(k1_tops_1('#skF_1', A_22), A_22) | ~r1_tarski(A_22, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_742])).
% 52.03/42.40  tff(c_983, plain, (![A_120]: (r1_tarski(k3_subset_1(A_120, A_120), A_120))), inference(demodulation, [status(thm), theory('equality')], [c_891, c_891, c_68])).
% 52.03/42.40  tff(c_992, plain, (r1_tarski(k3_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_983, c_762])).
% 52.03/42.40  tff(c_19467, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_992, c_19429])).
% 52.03/42.40  tff(c_19909, plain, (![A_487]: (r1_tarski(A_487, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_487, k3_subset_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_19467, c_8])).
% 52.03/42.40  tff(c_19933, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1('#skF_2', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k3_subset_1('#skF_2', '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_755, c_19909])).
% 52.03/42.40  tff(c_19955, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1('#skF_2', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19463, c_19933])).
% 52.03/42.40  tff(c_21462, plain, (r1_tarski(k1_xboole_0, k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_21454, c_19955])).
% 52.03/42.40  tff(c_23748, plain, (![A_545]: (r1_tarski(A_545, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_545, k1_xboole_0))), inference(resolution, [status(thm)], [c_21462, c_8])).
% 52.03/42.40  tff(c_23811, plain, (![A_545]: (k1_tops_1('#skF_1', '#skF_2')=A_545 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), A_545) | ~r1_tarski(A_545, k1_xboole_0))), inference(resolution, [status(thm)], [c_23748, c_2])).
% 52.03/42.40  tff(c_193538, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_xboole_0) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_193516, c_23811])).
% 52.03/42.40  tff(c_193631, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_104, c_101, c_6, c_69046, c_101, c_6, c_23544, c_23544, c_193538])).
% 52.03/42.40  tff(c_193633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1170, c_193631])).
% 52.03/42.40  tff(c_193634, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_1169])).
% 52.03/42.40  tff(c_194131, plain, (![A_1709, B_1710]: (v1_tops_1(k3_subset_1(u1_struct_0(A_1709), B_1710), A_1709) | ~v2_tops_1(B_1710, A_1709) | ~m1_subset_1(B_1710, k1_zfmisc_1(u1_struct_0(A_1709))) | ~l1_pre_topc(A_1709))), inference(cnfTransformation, [status(thm)], [f_123])).
% 52.03/42.40  tff(c_194146, plain, (![B_1710]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_1710), '#skF_1') | ~v2_tops_1(B_1710, '#skF_1') | ~m1_subset_1(B_1710, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_194131])).
% 52.03/42.40  tff(c_194157, plain, (![B_1711]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_1711), '#skF_1') | ~v2_tops_1(B_1711, '#skF_1') | ~m1_subset_1(B_1711, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_194146])).
% 52.03/42.40  tff(c_60, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 52.03/42.40  tff(c_103, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_60])).
% 52.03/42.40  tff(c_194160, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_194157, c_103])).
% 52.03/42.40  tff(c_194179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_193634, c_194160])).
% 52.03/42.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.03/42.40  
% 52.03/42.40  Inference rules
% 52.03/42.40  ----------------------
% 52.03/42.40  #Ref     : 0
% 52.03/42.40  #Sup     : 42836
% 52.03/42.40  #Fact    : 0
% 52.03/42.40  #Define  : 0
% 52.03/42.40  #Split   : 52
% 52.03/42.40  #Chain   : 0
% 52.03/42.40  #Close   : 0
% 52.03/42.40  
% 52.03/42.40  Ordering : KBO
% 52.03/42.40  
% 52.03/42.40  Simplification rules
% 52.03/42.40  ----------------------
% 52.03/42.40  #Subsume      : 16169
% 52.03/42.40  #Demod        : 38485
% 52.03/42.40  #Tautology    : 11478
% 52.03/42.40  #SimpNegUnit  : 465
% 52.03/42.40  #BackRed      : 123
% 52.03/42.40  
% 52.03/42.40  #Partial instantiations: 0
% 52.03/42.40  #Strategies tried      : 1
% 52.03/42.40  
% 52.03/42.40  Timing (in seconds)
% 52.03/42.40  ----------------------
% 52.03/42.40  Preprocessing        : 0.37
% 52.03/42.40  Parsing              : 0.20
% 52.03/42.40  CNF conversion       : 0.03
% 52.03/42.40  Main loop            : 41.23
% 52.03/42.40  Inferencing          : 4.11
% 52.03/42.40  Reduction            : 13.51
% 52.03/42.40  Demodulation         : 10.52
% 52.03/42.40  BG Simplification    : 0.36
% 52.03/42.40  Subsumption          : 21.66
% 52.03/42.40  Abstraction          : 0.63
% 52.03/42.40  MUC search           : 0.00
% 52.03/42.40  Cooper               : 0.00
% 52.03/42.40  Total                : 41.66
% 52.03/42.40  Index Insertion      : 0.00
% 52.03/42.40  Index Deletion       : 0.00
% 52.03/42.40  Index Matching       : 0.00
% 52.03/42.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
