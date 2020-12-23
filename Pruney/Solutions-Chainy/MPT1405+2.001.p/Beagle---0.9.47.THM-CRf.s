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
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 23.52s
% Output     : CNFRefutation 23.52s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 242 expanded)
%              Number of leaves         :   41 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 466 expanded)
%              Number of equality atoms :   30 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_118,axiom,(
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

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_56,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    ! [A_35] :
      ( l1_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_91,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_95,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_96,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_106,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_96])).

tff(c_111,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_106])).

tff(c_112,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_58])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_22,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_463,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1(k3_subset_1(A_113,B_114),k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1335,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k3_subset_1(A_152,B_153),A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(resolution,[status(thm)],[c_463,c_34])).

tff(c_30,plain,(
    ! [A_21,C_24,B_22] :
      ( r1_tarski(k3_subset_1(A_21,C_24),B_22)
      | ~ r1_tarski(k3_subset_1(A_21,B_22),C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1340,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k3_subset_1(A_152,A_152),B_153)
      | ~ m1_subset_1(A_152,k1_zfmisc_1(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(resolution,[status(thm)],[c_1335,c_30])).

tff(c_1571,plain,(
    ! [A_162,B_163] :
      ( r1_tarski(k3_subset_1(A_162,A_162),B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_162)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1340])).

tff(c_107,plain,(
    ! [A_25] : r1_tarski(k1_xboole_0,A_25) ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_127,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_107,c_127])).

tff(c_1599,plain,(
    ! [A_162] :
      ( k3_subset_1(A_162,A_162) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_162)) ) ),
    inference(resolution,[status(thm)],[c_1571,c_135])).

tff(c_1622,plain,(
    ! [A_162] : k3_subset_1(A_162,A_162) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1599])).

tff(c_347,plain,(
    ! [A_102,B_103] :
      ( k3_subset_1(A_102,k3_subset_1(A_102,B_103)) = B_103
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_359,plain,(
    ! [A_16] : k3_subset_1(A_16,k3_subset_1(A_16,A_16)) = A_16 ),
    inference(resolution,[status(thm)],[c_65,c_347])).

tff(c_1627,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1622,c_359])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_778,plain,(
    ! [B_126,A_127] :
      ( v4_pre_topc(B_126,A_127)
      | ~ v1_xboole_0(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_797,plain,(
    ! [B_126] :
      ( v4_pre_topc(B_126,'#skF_3')
      | ~ v1_xboole_0(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_778])).

tff(c_818,plain,(
    ! [B_129] :
      ( v4_pre_topc(B_129,'#skF_3')
      | ~ v1_xboole_0(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_797])).

tff(c_841,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_818])).

tff(c_855,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_841])).

tff(c_614,plain,(
    ! [A_119,B_120] :
      ( k2_pre_topc(A_119,B_120) = B_120
      | ~ v4_pre_topc(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_633,plain,(
    ! [B_120] :
      ( k2_pre_topc('#skF_3',B_120) = B_120
      | ~ v4_pre_topc(B_120,'#skF_3')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_614])).

tff(c_694,plain,(
    ! [B_123] :
      ( k2_pre_topc('#skF_3',B_123) = B_123
      | ~ v4_pre_topc(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_633])).

tff(c_727,plain,
    ( k2_pre_topc('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_694])).

tff(c_817,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_817])).

tff(c_859,plain,(
    k2_pre_topc('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_1629,plain,(
    ! [A_164] : k3_subset_1(A_164,A_164) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1599])).

tff(c_1297,plain,(
    ! [A_150,B_151] :
      ( k3_subset_1(u1_struct_0(A_150),k2_pre_topc(A_150,k3_subset_1(u1_struct_0(A_150),B_151))) = k1_tops_1(A_150,B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1325,plain,(
    ! [B_151] :
      ( k3_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),B_151))) = k1_tops_1('#skF_3',B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1297])).

tff(c_1332,plain,(
    ! [B_151] :
      ( k3_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k3_subset_1(k2_struct_0('#skF_3'),B_151))) = k1_tops_1('#skF_3',B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_95,c_95,c_1325])).

tff(c_1635,plain,
    ( k3_subset_1(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k1_xboole_0)) = k1_tops_1('#skF_3',k2_struct_0('#skF_3'))
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1629,c_1332])).

tff(c_1671,plain,(
    k3_subset_1(k2_struct_0('#skF_3'),k1_xboole_0) = k1_tops_1('#skF_3',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_859,c_1635])).

tff(c_1792,plain,(
    k1_tops_1('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1627,c_1671])).

tff(c_1986,plain,(
    ! [C_175,A_176,B_177] :
      ( m2_connsp_2(C_175,A_176,B_177)
      | ~ r1_tarski(B_177,k1_tops_1(A_176,C_175))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1988,plain,(
    ! [B_177] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_177)
      | ~ r1_tarski(B_177,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1792,c_1986])).

tff(c_67411,plain,(
    ! [B_1041] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_1041)
      | ~ r1_tarski(B_1041,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1041,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_65,c_95,c_1988])).

tff(c_67460,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_112,c_67411])).

tff(c_67487,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_67460])).

tff(c_67489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_67487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.52/13.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.52/13.91  
% 23.52/13.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.52/13.91  %$ m2_connsp_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 23.52/13.91  
% 23.52/13.91  %Foreground sorts:
% 23.52/13.91  
% 23.52/13.91  
% 23.52/13.91  %Background operators:
% 23.52/13.91  
% 23.52/13.91  
% 23.52/13.91  %Foreground operators:
% 23.52/13.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 23.52/13.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.52/13.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.52/13.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.52/13.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.52/13.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.52/13.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.52/13.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.52/13.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 23.52/13.91  tff('#skF_3', type, '#skF_3': $i).
% 23.52/13.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.52/13.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 23.52/13.91  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.52/13.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.52/13.91  tff('#skF_4', type, '#skF_4': $i).
% 23.52/13.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.52/13.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 23.52/13.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.52/13.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.52/13.91  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 23.52/13.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 23.52/13.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.52/13.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.52/13.91  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 23.52/13.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.52/13.91  
% 23.52/13.93  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 23.52/13.93  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 23.52/13.93  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 23.52/13.93  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 23.52/13.93  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 23.52/13.93  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 23.52/13.93  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 23.52/13.93  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 23.52/13.93  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 23.52/13.93  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.52/13.93  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 23.52/13.93  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.52/13.93  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 23.52/13.93  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 23.52/13.93  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 23.52/13.93  tff(f_139, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 23.52/13.93  tff(c_56, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 23.52/13.93  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 23.52/13.93  tff(c_44, plain, (![A_35]: (l1_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.52/13.93  tff(c_86, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 23.52/13.93  tff(c_91, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_44, c_86])).
% 23.52/13.93  tff(c_95, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_91])).
% 23.52/13.93  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 23.52/13.93  tff(c_96, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.52/13.93  tff(c_106, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_96])).
% 23.52/13.93  tff(c_111, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_106])).
% 23.52/13.93  tff(c_112, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_58])).
% 23.52/13.93  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 23.52/13.93  tff(c_22, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.52/13.93  tff(c_24, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.52/13.93  tff(c_65, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 23.52/13.93  tff(c_32, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 23.52/13.93  tff(c_463, plain, (![A_113, B_114]: (m1_subset_1(k3_subset_1(A_113, B_114), k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.52/13.93  tff(c_34, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.52/13.93  tff(c_1335, plain, (![A_152, B_153]: (r1_tarski(k3_subset_1(A_152, B_153), A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(resolution, [status(thm)], [c_463, c_34])).
% 23.52/13.93  tff(c_30, plain, (![A_21, C_24, B_22]: (r1_tarski(k3_subset_1(A_21, C_24), B_22) | ~r1_tarski(k3_subset_1(A_21, B_22), C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 23.52/13.93  tff(c_1340, plain, (![A_152, B_153]: (r1_tarski(k3_subset_1(A_152, A_152), B_153) | ~m1_subset_1(A_152, k1_zfmisc_1(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(resolution, [status(thm)], [c_1335, c_30])).
% 23.52/13.93  tff(c_1571, plain, (![A_162, B_163]: (r1_tarski(k3_subset_1(A_162, A_162), B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(A_162)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1340])).
% 23.52/13.93  tff(c_107, plain, (![A_25]: (r1_tarski(k1_xboole_0, A_25))), inference(resolution, [status(thm)], [c_32, c_96])).
% 23.52/13.93  tff(c_127, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.52/13.93  tff(c_135, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_107, c_127])).
% 23.52/13.93  tff(c_1599, plain, (![A_162]: (k3_subset_1(A_162, A_162)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_162)))), inference(resolution, [status(thm)], [c_1571, c_135])).
% 23.52/13.93  tff(c_1622, plain, (![A_162]: (k3_subset_1(A_162, A_162)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1599])).
% 23.52/13.93  tff(c_347, plain, (![A_102, B_103]: (k3_subset_1(A_102, k3_subset_1(A_102, B_103))=B_103 | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.52/13.93  tff(c_359, plain, (![A_16]: (k3_subset_1(A_16, k3_subset_1(A_16, A_16))=A_16)), inference(resolution, [status(thm)], [c_65, c_347])).
% 23.52/13.93  tff(c_1627, plain, (![A_16]: (k3_subset_1(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_1622, c_359])).
% 23.52/13.93  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.52/13.93  tff(c_778, plain, (![B_126, A_127]: (v4_pre_topc(B_126, A_127) | ~v1_xboole_0(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.52/13.93  tff(c_797, plain, (![B_126]: (v4_pre_topc(B_126, '#skF_3') | ~v1_xboole_0(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_778])).
% 23.52/13.93  tff(c_818, plain, (![B_129]: (v4_pre_topc(B_129, '#skF_3') | ~v1_xboole_0(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_797])).
% 23.52/13.93  tff(c_841, plain, (v4_pre_topc(k1_xboole_0, '#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_818])).
% 23.52/13.93  tff(c_855, plain, (v4_pre_topc(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_841])).
% 23.52/13.93  tff(c_614, plain, (![A_119, B_120]: (k2_pre_topc(A_119, B_120)=B_120 | ~v4_pre_topc(B_120, A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.52/13.93  tff(c_633, plain, (![B_120]: (k2_pre_topc('#skF_3', B_120)=B_120 | ~v4_pre_topc(B_120, '#skF_3') | ~m1_subset_1(B_120, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_614])).
% 23.52/13.93  tff(c_694, plain, (![B_123]: (k2_pre_topc('#skF_3', B_123)=B_123 | ~v4_pre_topc(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_633])).
% 23.52/13.93  tff(c_727, plain, (k2_pre_topc('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_32, c_694])).
% 23.52/13.93  tff(c_817, plain, (~v4_pre_topc(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_727])).
% 23.52/13.93  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_855, c_817])).
% 23.52/13.93  tff(c_859, plain, (k2_pre_topc('#skF_3', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_727])).
% 23.52/13.93  tff(c_1629, plain, (![A_164]: (k3_subset_1(A_164, A_164)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1599])).
% 23.52/13.93  tff(c_1297, plain, (![A_150, B_151]: (k3_subset_1(u1_struct_0(A_150), k2_pre_topc(A_150, k3_subset_1(u1_struct_0(A_150), B_151)))=k1_tops_1(A_150, B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_125])).
% 23.52/13.93  tff(c_1325, plain, (![B_151]: (k3_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), B_151)))=k1_tops_1('#skF_3', B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_1297])).
% 23.52/13.93  tff(c_1332, plain, (![B_151]: (k3_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k3_subset_1(k2_struct_0('#skF_3'), B_151)))=k1_tops_1('#skF_3', B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_95, c_95, c_1325])).
% 23.52/13.93  tff(c_1635, plain, (k3_subset_1(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k1_xboole_0))=k1_tops_1('#skF_3', k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1629, c_1332])).
% 23.52/13.93  tff(c_1671, plain, (k3_subset_1(k2_struct_0('#skF_3'), k1_xboole_0)=k1_tops_1('#skF_3', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_859, c_1635])).
% 23.52/13.93  tff(c_1792, plain, (k1_tops_1('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1627, c_1671])).
% 23.52/13.93  tff(c_1986, plain, (![C_175, A_176, B_177]: (m2_connsp_2(C_175, A_176, B_177) | ~r1_tarski(B_177, k1_tops_1(A_176, C_175)) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_139])).
% 23.52/13.93  tff(c_1988, plain, (![B_177]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_177) | ~r1_tarski(B_177, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1792, c_1986])).
% 23.52/13.93  tff(c_67411, plain, (![B_1041]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_1041) | ~r1_tarski(B_1041, k2_struct_0('#skF_3')) | ~m1_subset_1(B_1041, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_65, c_95, c_1988])).
% 23.52/13.93  tff(c_67460, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_112, c_67411])).
% 23.52/13.93  tff(c_67487, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_67460])).
% 23.52/13.93  tff(c_67489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_67487])).
% 23.52/13.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.52/13.93  
% 23.52/13.93  Inference rules
% 23.52/13.93  ----------------------
% 23.52/13.93  #Ref     : 0
% 23.52/13.93  #Sup     : 16343
% 23.52/13.93  #Fact    : 0
% 23.52/13.93  #Define  : 0
% 23.52/13.93  #Split   : 22
% 23.52/13.93  #Chain   : 0
% 23.52/13.93  #Close   : 0
% 23.52/13.93  
% 23.52/13.93  Ordering : KBO
% 23.52/13.93  
% 23.52/13.93  Simplification rules
% 23.52/13.93  ----------------------
% 23.52/13.93  #Subsume      : 6092
% 23.52/13.93  #Demod        : 10707
% 23.52/13.93  #Tautology    : 3473
% 23.52/13.93  #SimpNegUnit  : 413
% 23.52/13.93  #BackRed      : 23
% 23.52/13.93  
% 23.52/13.93  #Partial instantiations: 0
% 23.52/13.93  #Strategies tried      : 1
% 23.52/13.93  
% 23.52/13.93  Timing (in seconds)
% 23.52/13.93  ----------------------
% 23.52/13.93  Preprocessing        : 0.35
% 23.52/13.93  Parsing              : 0.18
% 23.52/13.93  CNF conversion       : 0.03
% 23.52/13.93  Main loop            : 12.77
% 23.52/13.93  Inferencing          : 1.93
% 23.52/13.93  Reduction            : 3.16
% 23.52/13.93  Demodulation         : 2.23
% 23.52/13.93  BG Simplification    : 0.21
% 23.52/13.93  Subsumption          : 6.74
% 23.52/13.93  Abstraction          : 0.35
% 23.52/13.93  MUC search           : 0.00
% 23.52/13.93  Cooper               : 0.00
% 23.52/13.93  Total                : 13.16
% 23.52/13.93  Index Insertion      : 0.00
% 23.52/13.93  Index Deletion       : 0.00
% 23.52/13.93  Index Matching       : 0.00
% 23.52/13.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
