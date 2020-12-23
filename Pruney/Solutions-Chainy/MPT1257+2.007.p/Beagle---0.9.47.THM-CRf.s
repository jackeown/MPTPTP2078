%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:58 EST 2020

% Result     : Theorem 56.29s
% Output     : CNFRefutation 56.45s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 427 expanded)
%              Number of leaves         :   33 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 880 expanded)
%              Number of equality atoms :   24 ( 150 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(c_48,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_70,B_71] :
      ( k3_subset_1(A_70,k3_subset_1(A_70,B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_977,plain,(
    ! [B_147,C_148,A_149] :
      ( r1_xboole_0(B_147,C_148)
      | ~ r1_tarski(B_147,k3_subset_1(A_149,C_148))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(A_149))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1165,plain,(
    ! [A_151,C_152] :
      ( r1_xboole_0(k3_subset_1(A_151,C_152),C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_151))
      | ~ m1_subset_1(k3_subset_1(A_151,C_152),k1_zfmisc_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_6,c_977])).

tff(c_1173,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1165])).

tff(c_1182,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_114,c_1173])).

tff(c_1230,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1182])).

tff(c_1234,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_1230])).

tff(c_1241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1234])).

tff(c_1243,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1182])).

tff(c_40,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k2_pre_topc(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1868,plain,(
    ! [A_185,B_186] :
      ( k3_subset_1(u1_struct_0(A_185),k2_pre_topc(A_185,k3_subset_1(u1_struct_0(A_185),B_186))) = k1_tops_1(A_185,B_186)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_62419,plain,(
    ! [A_788,B_789] :
      ( m1_subset_1(k1_tops_1(A_788,B_789),k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ m1_subset_1(k2_pre_topc(A_788,k3_subset_1(u1_struct_0(A_788),B_789)),k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ m1_subset_1(B_789,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ l1_pre_topc(A_788) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_12])).

tff(c_129005,plain,(
    ! [A_1259,B_1260] :
      ( m1_subset_1(k1_tops_1(A_1259,B_1260),k1_zfmisc_1(u1_struct_0(A_1259)))
      | ~ m1_subset_1(B_1260,k1_zfmisc_1(u1_struct_0(A_1259)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_1259),B_1260),k1_zfmisc_1(u1_struct_0(A_1259)))
      | ~ l1_pre_topc(A_1259) ) ),
    inference(resolution,[status(thm)],[c_40,c_62419])).

tff(c_129069,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1243,c_129005])).

tff(c_129127,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_129069])).

tff(c_864,plain,(
    ! [A_143,B_144] :
      ( k2_tops_1(A_143,k3_subset_1(u1_struct_0(A_143),B_144)) = k2_tops_1(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_887,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_864])).

tff(c_902,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_887])).

tff(c_2629,plain,(
    ! [A_197,B_198] :
      ( k9_subset_1(u1_struct_0(A_197),k2_pre_topc(A_197,B_198),k2_pre_topc(A_197,k3_subset_1(u1_struct_0(A_197),B_198))) = k2_tops_1(A_197,B_198)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k9_subset_1(A_10,B_11,C_12),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61913,plain,(
    ! [A_770,B_771] :
      ( m1_subset_1(k2_tops_1(A_770,B_771),k1_zfmisc_1(u1_struct_0(A_770)))
      | ~ m1_subset_1(k2_pre_topc(A_770,k3_subset_1(u1_struct_0(A_770),B_771)),k1_zfmisc_1(u1_struct_0(A_770)))
      | ~ m1_subset_1(B_771,k1_zfmisc_1(u1_struct_0(A_770)))
      | ~ l1_pre_topc(A_770) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2629,c_14])).

tff(c_61962,plain,
    ( m1_subset_1(k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_61913])).

tff(c_61984,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1243,c_902,c_61962])).

tff(c_63985,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_61984])).

tff(c_63988,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_63985])).

tff(c_63995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_63988])).

tff(c_63996,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_61984])).

tff(c_115,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k3_subset_1(A_72,B_73),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_126,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k3_subset_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_115,c_36])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_251,plain,(
    ! [A_93,B_94] :
      ( k4_subset_1(A_93,B_94,k3_subset_1(A_93,B_94)) = k2_subset_1(A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_264,plain,(
    ! [B_95,A_96] :
      ( k4_subset_1(B_95,A_96,k3_subset_1(B_95,A_96)) = k2_subset_1(B_95)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_38,c_251])).

tff(c_276,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k2_subset_1(u1_struct_0('#skF_1'))
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_264])).

tff(c_941,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_944,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_126,c_941])).

tff(c_948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_944])).

tff(c_950,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_113,plain,(
    ! [B_45,A_44] :
      ( k3_subset_1(B_45,k3_subset_1(B_45,A_44)) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_161108,plain,(
    ! [A_1454,A_1455] :
      ( k3_subset_1(u1_struct_0(A_1454),k2_pre_topc(A_1454,A_1455)) = k1_tops_1(A_1454,k3_subset_1(u1_struct_0(A_1454),A_1455))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_1454),A_1455),k1_zfmisc_1(u1_struct_0(A_1454)))
      | ~ l1_pre_topc(A_1454)
      | ~ r1_tarski(A_1455,u1_struct_0(A_1454)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1868])).

tff(c_161202,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_161108])).

tff(c_161262,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_52,c_50,c_114,c_161202])).

tff(c_436,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k2_pre_topc(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_subset_1(A_13,k3_subset_1(A_13,B_14)) = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_454,plain,(
    ! [A_108,B_109] :
      ( k3_subset_1(u1_struct_0(A_108),k3_subset_1(u1_struct_0(A_108),k2_pre_topc(A_108,B_109))) = k2_pre_topc(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_436,c_16])).

tff(c_161622,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_161262,c_454])).

tff(c_161829,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1243,c_161622])).

tff(c_162199,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_161829,c_12])).

tff(c_162427,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129127,c_162199])).

tff(c_63997,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_61984])).

tff(c_30,plain,(
    ! [A_36,B_37,C_39] :
      ( r1_tarski(k3_subset_1(A_36,B_37),k3_subset_1(A_36,k9_subset_1(A_36,B_37,C_39)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68244,plain,(
    ! [A_855,B_856] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_855),k2_pre_topc(A_855,B_856)),k3_subset_1(u1_struct_0(A_855),k2_tops_1(A_855,B_856)))
      | ~ m1_subset_1(k2_pre_topc(A_855,k3_subset_1(u1_struct_0(A_855),B_856)),k1_zfmisc_1(u1_struct_0(A_855)))
      | ~ m1_subset_1(k2_pre_topc(A_855,B_856),k1_zfmisc_1(u1_struct_0(A_855)))
      | ~ m1_subset_1(B_856,k1_zfmisc_1(u1_struct_0(A_855)))
      | ~ l1_pre_topc(A_855) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2629,c_30])).

tff(c_68302,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_68244])).

tff(c_68326,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1243,c_63997,c_114,c_68302])).

tff(c_162663,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162427,c_161262,c_68326])).

tff(c_32,plain,(
    ! [B_41,C_43,A_40] :
      ( r1_xboole_0(B_41,C_43)
      | ~ r1_tarski(B_41,k3_subset_1(A_40,C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_162668,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_162663,c_32])).

tff(c_162683,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129127,c_63996,c_162668])).

tff(c_162685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_162683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.29/44.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.29/44.88  
% 56.29/44.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.29/44.88  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 56.29/44.88  
% 56.29/44.88  %Foreground sorts:
% 56.29/44.88  
% 56.29/44.88  
% 56.29/44.88  %Background operators:
% 56.29/44.88  
% 56.29/44.88  
% 56.29/44.88  %Foreground operators:
% 56.29/44.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.29/44.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 56.29/44.88  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 56.29/44.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 56.29/44.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.29/44.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 56.29/44.88  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 56.29/44.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 56.29/44.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 56.29/44.88  tff('#skF_2', type, '#skF_2': $i).
% 56.29/44.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 56.29/44.88  tff('#skF_1', type, '#skF_1': $i).
% 56.29/44.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 56.29/44.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.29/44.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.29/44.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 56.29/44.88  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 56.29/44.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 56.29/44.88  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 56.29/44.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 56.29/44.88  
% 56.45/44.90  tff(f_146, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 56.45/44.90  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 56.45/44.90  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 56.45/44.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.45/44.90  tff(f_107, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 56.45/44.90  tff(f_117, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 56.45/44.90  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 56.45/44.90  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 56.45/44.90  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 56.45/44.90  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 56.45/44.90  tff(f_111, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 56.45/44.90  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 56.45/44.90  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 56.45/44.90  tff(c_48, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 56.45/44.90  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 56.45/44.90  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 56.45/44.90  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 56.45/44.90  tff(c_108, plain, (![A_70, B_71]: (k3_subset_1(A_70, k3_subset_1(A_70, B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.45/44.90  tff(c_114, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_50, c_108])).
% 56.45/44.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.45/44.90  tff(c_977, plain, (![B_147, C_148, A_149]: (r1_xboole_0(B_147, C_148) | ~r1_tarski(B_147, k3_subset_1(A_149, C_148)) | ~m1_subset_1(C_148, k1_zfmisc_1(A_149)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.45/44.90  tff(c_1165, plain, (![A_151, C_152]: (r1_xboole_0(k3_subset_1(A_151, C_152), C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(A_151)) | ~m1_subset_1(k3_subset_1(A_151, C_152), k1_zfmisc_1(A_151)))), inference(resolution, [status(thm)], [c_6, c_977])).
% 56.45/44.90  tff(c_1173, plain, (r1_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1165])).
% 56.45/44.90  tff(c_1182, plain, (r1_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_114, c_1173])).
% 56.45/44.90  tff(c_1230, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1182])).
% 56.45/44.90  tff(c_1234, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_1230])).
% 56.45/44.90  tff(c_1241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1234])).
% 56.45/44.90  tff(c_1243, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1182])).
% 56.45/44.90  tff(c_40, plain, (![A_46, B_47]: (m1_subset_1(k2_pre_topc(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_117])).
% 56.45/44.90  tff(c_1868, plain, (![A_185, B_186]: (k3_subset_1(u1_struct_0(A_185), k2_pre_topc(A_185, k3_subset_1(u1_struct_0(A_185), B_186)))=k1_tops_1(A_185, B_186) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_124])).
% 56.45/44.90  tff(c_62419, plain, (![A_788, B_789]: (m1_subset_1(k1_tops_1(A_788, B_789), k1_zfmisc_1(u1_struct_0(A_788))) | ~m1_subset_1(k2_pre_topc(A_788, k3_subset_1(u1_struct_0(A_788), B_789)), k1_zfmisc_1(u1_struct_0(A_788))) | ~m1_subset_1(B_789, k1_zfmisc_1(u1_struct_0(A_788))) | ~l1_pre_topc(A_788))), inference(superposition, [status(thm), theory('equality')], [c_1868, c_12])).
% 56.45/44.90  tff(c_129005, plain, (![A_1259, B_1260]: (m1_subset_1(k1_tops_1(A_1259, B_1260), k1_zfmisc_1(u1_struct_0(A_1259))) | ~m1_subset_1(B_1260, k1_zfmisc_1(u1_struct_0(A_1259))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_1259), B_1260), k1_zfmisc_1(u1_struct_0(A_1259))) | ~l1_pre_topc(A_1259))), inference(resolution, [status(thm)], [c_40, c_62419])).
% 56.45/44.90  tff(c_129069, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1243, c_129005])).
% 56.45/44.90  tff(c_129127, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_129069])).
% 56.45/44.90  tff(c_864, plain, (![A_143, B_144]: (k2_tops_1(A_143, k3_subset_1(u1_struct_0(A_143), B_144))=k2_tops_1(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_138])).
% 56.45/44.90  tff(c_887, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_864])).
% 56.45/44.90  tff(c_902, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_887])).
% 56.45/44.90  tff(c_2629, plain, (![A_197, B_198]: (k9_subset_1(u1_struct_0(A_197), k2_pre_topc(A_197, B_198), k2_pre_topc(A_197, k3_subset_1(u1_struct_0(A_197), B_198)))=k2_tops_1(A_197, B_198) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_131])).
% 56.45/44.90  tff(c_14, plain, (![A_10, B_11, C_12]: (m1_subset_1(k9_subset_1(A_10, B_11, C_12), k1_zfmisc_1(A_10)) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.45/44.90  tff(c_61913, plain, (![A_770, B_771]: (m1_subset_1(k2_tops_1(A_770, B_771), k1_zfmisc_1(u1_struct_0(A_770))) | ~m1_subset_1(k2_pre_topc(A_770, k3_subset_1(u1_struct_0(A_770), B_771)), k1_zfmisc_1(u1_struct_0(A_770))) | ~m1_subset_1(B_771, k1_zfmisc_1(u1_struct_0(A_770))) | ~l1_pre_topc(A_770))), inference(superposition, [status(thm), theory('equality')], [c_2629, c_14])).
% 56.45/44.90  tff(c_61962, plain, (m1_subset_1(k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_114, c_61913])).
% 56.45/44.90  tff(c_61984, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1243, c_902, c_61962])).
% 56.45/44.90  tff(c_63985, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_61984])).
% 56.45/44.90  tff(c_63988, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_63985])).
% 56.45/44.90  tff(c_63995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_63988])).
% 56.45/44.90  tff(c_63996, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_61984])).
% 56.45/44.90  tff(c_115, plain, (![A_72, B_73]: (m1_subset_1(k3_subset_1(A_72, B_73), k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 56.45/44.90  tff(c_36, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 56.45/44.90  tff(c_126, plain, (![A_72, B_73]: (r1_tarski(k3_subset_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(resolution, [status(thm)], [c_115, c_36])).
% 56.45/44.90  tff(c_38, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_111])).
% 56.45/44.90  tff(c_251, plain, (![A_93, B_94]: (k4_subset_1(A_93, B_94, k3_subset_1(A_93, B_94))=k2_subset_1(A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 56.45/44.90  tff(c_264, plain, (![B_95, A_96]: (k4_subset_1(B_95, A_96, k3_subset_1(B_95, A_96))=k2_subset_1(B_95) | ~r1_tarski(A_96, B_95))), inference(resolution, [status(thm)], [c_38, c_251])).
% 56.45/44.90  tff(c_276, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k2_subset_1(u1_struct_0('#skF_1')) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_264])).
% 56.45/44.90  tff(c_941, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_276])).
% 56.45/44.90  tff(c_944, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_126, c_941])).
% 56.45/44.90  tff(c_948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_944])).
% 56.45/44.90  tff(c_950, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_276])).
% 56.45/44.90  tff(c_113, plain, (![B_45, A_44]: (k3_subset_1(B_45, k3_subset_1(B_45, A_44))=A_44 | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_38, c_108])).
% 56.45/44.90  tff(c_161108, plain, (![A_1454, A_1455]: (k3_subset_1(u1_struct_0(A_1454), k2_pre_topc(A_1454, A_1455))=k1_tops_1(A_1454, k3_subset_1(u1_struct_0(A_1454), A_1455)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_1454), A_1455), k1_zfmisc_1(u1_struct_0(A_1454))) | ~l1_pre_topc(A_1454) | ~r1_tarski(A_1455, u1_struct_0(A_1454)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1868])).
% 56.45/44.90  tff(c_161202, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_161108])).
% 56.45/44.90  tff(c_161262, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_950, c_52, c_50, c_114, c_161202])).
% 56.45/44.90  tff(c_436, plain, (![A_108, B_109]: (m1_subset_1(k2_pre_topc(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_117])).
% 56.45/44.90  tff(c_16, plain, (![A_13, B_14]: (k3_subset_1(A_13, k3_subset_1(A_13, B_14))=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.45/44.90  tff(c_454, plain, (![A_108, B_109]: (k3_subset_1(u1_struct_0(A_108), k3_subset_1(u1_struct_0(A_108), k2_pre_topc(A_108, B_109)))=k2_pre_topc(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_436, c_16])).
% 56.45/44.90  tff(c_161622, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_161262, c_454])).
% 56.45/44.90  tff(c_161829, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1243, c_161622])).
% 56.45/44.90  tff(c_162199, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_161829, c_12])).
% 56.45/44.90  tff(c_162427, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_129127, c_162199])).
% 56.45/44.90  tff(c_63997, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_61984])).
% 56.45/44.90  tff(c_30, plain, (![A_36, B_37, C_39]: (r1_tarski(k3_subset_1(A_36, B_37), k3_subset_1(A_36, k9_subset_1(A_36, B_37, C_39))) | ~m1_subset_1(C_39, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 56.45/44.90  tff(c_68244, plain, (![A_855, B_856]: (r1_tarski(k3_subset_1(u1_struct_0(A_855), k2_pre_topc(A_855, B_856)), k3_subset_1(u1_struct_0(A_855), k2_tops_1(A_855, B_856))) | ~m1_subset_1(k2_pre_topc(A_855, k3_subset_1(u1_struct_0(A_855), B_856)), k1_zfmisc_1(u1_struct_0(A_855))) | ~m1_subset_1(k2_pre_topc(A_855, B_856), k1_zfmisc_1(u1_struct_0(A_855))) | ~m1_subset_1(B_856, k1_zfmisc_1(u1_struct_0(A_855))) | ~l1_pre_topc(A_855))), inference(superposition, [status(thm), theory('equality')], [c_2629, c_30])).
% 56.45/44.90  tff(c_68302, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_902, c_68244])).
% 56.45/44.90  tff(c_68326, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1243, c_63997, c_114, c_68302])).
% 56.45/44.90  tff(c_162663, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_162427, c_161262, c_68326])).
% 56.45/44.90  tff(c_32, plain, (![B_41, C_43, A_40]: (r1_xboole_0(B_41, C_43) | ~r1_tarski(B_41, k3_subset_1(A_40, C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.45/44.90  tff(c_162668, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_162663, c_32])).
% 56.45/44.90  tff(c_162683, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_129127, c_63996, c_162668])).
% 56.45/44.90  tff(c_162685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_162683])).
% 56.45/44.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.45/44.90  
% 56.45/44.90  Inference rules
% 56.45/44.90  ----------------------
% 56.45/44.90  #Ref     : 0
% 56.45/44.90  #Sup     : 37696
% 56.45/44.90  #Fact    : 0
% 56.45/44.90  #Define  : 0
% 56.45/44.90  #Split   : 62
% 56.45/44.90  #Chain   : 0
% 56.45/44.90  #Close   : 0
% 56.45/44.90  
% 56.45/44.90  Ordering : KBO
% 56.45/44.90  
% 56.45/44.90  Simplification rules
% 56.45/44.90  ----------------------
% 56.45/44.90  #Subsume      : 3351
% 56.45/44.90  #Demod        : 35492
% 56.45/44.90  #Tautology    : 10784
% 56.45/44.90  #SimpNegUnit  : 98
% 56.45/44.90  #BackRed      : 243
% 56.45/44.90  
% 56.45/44.90  #Partial instantiations: 0
% 56.45/44.90  #Strategies tried      : 1
% 56.45/44.90  
% 56.45/44.90  Timing (in seconds)
% 56.45/44.90  ----------------------
% 56.45/44.90  Preprocessing        : 0.36
% 56.45/44.90  Parsing              : 0.20
% 56.45/44.90  CNF conversion       : 0.02
% 56.45/44.90  Main loop            : 43.72
% 56.45/44.90  Inferencing          : 5.56
% 56.45/44.90  Reduction            : 25.14
% 56.45/44.90  Demodulation         : 22.42
% 56.45/44.90  BG Simplification    : 0.65
% 56.45/44.90  Subsumption          : 10.25
% 56.45/44.90  Abstraction          : 1.13
% 56.45/44.90  MUC search           : 0.00
% 56.45/44.90  Cooper               : 0.00
% 56.45/44.90  Total                : 44.12
% 56.45/44.90  Index Insertion      : 0.00
% 56.45/44.90  Index Deletion       : 0.00
% 56.45/44.90  Index Matching       : 0.00
% 56.45/44.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
