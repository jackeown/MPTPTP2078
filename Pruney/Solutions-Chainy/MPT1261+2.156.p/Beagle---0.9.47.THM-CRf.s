%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 10.77s
% Output     : CNFRefutation 10.83s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 417 expanded)
%              Number of leaves         :   46 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          :  251 ( 710 expanded)
%              Number of equality atoms :  116 ( 255 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_14436,plain,(
    ! [A_513,B_514,C_515] :
      ( k7_subset_1(A_513,B_514,C_515) = k4_xboole_0(B_514,C_515)
      | ~ m1_subset_1(B_514,k1_zfmisc_1(A_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14449,plain,(
    ! [C_515] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_515) = k4_xboole_0('#skF_2',C_515) ),
    inference(resolution,[status(thm)],[c_54,c_14436])).

tff(c_60,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_182,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2479,plain,(
    ! [A_183,B_184] :
      ( k4_subset_1(u1_struct_0(A_183),B_184,k2_tops_1(A_183,B_184)) = k2_pre_topc(A_183,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2487,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2479])).

tff(c_2498,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2487])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1754,plain,(
    ! [A_154,B_155,C_156] :
      ( k7_subset_1(A_154,B_155,C_156) = k4_xboole_0(B_155,C_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1816,plain,(
    ! [C_161] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_161) = k4_xboole_0('#skF_2',C_161) ),
    inference(resolution,[status(thm)],[c_54,c_1754])).

tff(c_66,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_92,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1822,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1816,c_92])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2125,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_18])).

tff(c_155,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_169,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_155])).

tff(c_416,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,C_86)
      | ~ r1_tarski(B_87,C_86)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_445,plain,(
    ! [A_90] :
      ( r1_tarski(A_90,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_90,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_169,c_416])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_456,plain,(
    ! [A_8,A_90] :
      ( r1_tarski(A_8,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_8,A_90)
      | ~ r1_tarski(A_90,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_445,c_14])).

tff(c_2134,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2125,c_456])).

tff(c_2147,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2134])).

tff(c_42,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2176,plain,(
    ! [A_171,B_172,C_173] :
      ( k4_subset_1(A_171,B_172,C_173) = k2_xboole_0(B_172,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5330,plain,(
    ! [B_261,B_262,A_263] :
      ( k4_subset_1(B_261,B_262,A_263) = k2_xboole_0(B_262,A_263)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(B_261))
      | ~ r1_tarski(A_263,B_261) ) ),
    inference(resolution,[status(thm)],[c_42,c_2176])).

tff(c_5575,plain,(
    ! [A_269] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_269) = k2_xboole_0('#skF_2',A_269)
      | ~ r1_tarski(A_269,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_5330])).

tff(c_5605,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2147,c_5575])).

tff(c_5649,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_5605])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_61,B_62] : k2_xboole_0(k4_xboole_0(A_61,B_62),A_61) = A_61 ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_128,plain,(
    ! [B_62] : k4_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_12])).

tff(c_343,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_352,plain,(
    ! [B_62] : k5_xboole_0(B_62,k1_xboole_0) = k2_xboole_0(B_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_343])).

tff(c_355,plain,(
    ! [B_62] : k5_xboole_0(B_62,k1_xboole_0) = B_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_352])).

tff(c_38,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_966,plain,(
    ! [A_130,B_131] :
      ( k4_xboole_0(A_130,B_131) = k3_subset_1(A_130,B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_983,plain,(
    ! [A_132] : k4_xboole_0(A_132,k1_xboole_0) = k3_subset_1(A_132,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_966])).

tff(c_100,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_1033,plain,(
    ! [A_132] : k2_xboole_0(k3_subset_1(A_132,k1_xboole_0),A_132) = A_132 ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_100])).

tff(c_742,plain,(
    ! [A_119,B_120] :
      ( k3_subset_1(A_119,k3_subset_1(A_119,B_120)) = B_120
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_753,plain,(
    ! [A_33] : k3_subset_1(A_33,k3_subset_1(A_33,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_742])).

tff(c_1036,plain,(
    ! [A_132] : r1_tarski(k3_subset_1(A_132,k1_xboole_0),A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_18])).

tff(c_2985,plain,(
    ! [B_201,A_202] :
      ( k4_xboole_0(B_201,A_202) = k3_subset_1(B_201,A_202)
      | ~ r1_tarski(A_202,B_201) ) ),
    inference(resolution,[status(thm)],[c_42,c_966])).

tff(c_3039,plain,(
    ! [A_132] : k4_xboole_0(A_132,k3_subset_1(A_132,k1_xboole_0)) = k3_subset_1(A_132,k3_subset_1(A_132,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1036,c_2985])).

tff(c_3226,plain,(
    ! [A_204] : k4_xboole_0(A_204,k3_subset_1(A_204,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_3039])).

tff(c_20,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3298,plain,(
    ! [A_204] : k5_xboole_0(k3_subset_1(A_204,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k3_subset_1(A_204,k1_xboole_0),A_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_3226,c_20])).

tff(c_3342,plain,(
    ! [A_204] : k3_subset_1(A_204,k1_xboole_0) = A_204 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_355,c_3298])).

tff(c_3372,plain,(
    ! [A_33] : k3_subset_1(A_33,A_33) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_753])).

tff(c_22,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_20] : m1_subset_1(k2_subset_1(A_20),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_20] : m1_subset_1(A_20,k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_982,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_subset_1(A_20,A_20) ),
    inference(resolution,[status(thm)],[c_67,c_966])).

tff(c_216,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_232,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_303,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_318,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_303])).

tff(c_1152,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_318])).

tff(c_3625,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3372,c_1152])).

tff(c_392,plain,(
    ! [A_83,B_84] : k3_xboole_0(k4_xboole_0(A_83,B_84),A_83) = k4_xboole_0(A_83,B_84) ),
    inference(resolution,[status(thm)],[c_18,c_216])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_398,plain,(
    ! [A_83,B_84] : k5_xboole_0(k4_xboole_0(A_83,B_84),k4_xboole_0(A_83,B_84)) = k4_xboole_0(k4_xboole_0(A_83,B_84),A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_8])).

tff(c_11814,plain,(
    ! [A_392,B_393] : k4_xboole_0(k4_xboole_0(A_392,B_393),A_392) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_398])).

tff(c_12038,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_11814])).

tff(c_12325,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12038,c_20])).

tff(c_12372,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5649,c_355,c_12325])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1966,plain,(
    ! [A_166,B_167] :
      ( v4_pre_topc(k2_pre_topc(A_166,B_167),A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1974,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1966])).

tff(c_1985,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1974])).

tff(c_12379,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12372,c_1985])).

tff(c_12381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_12379])).

tff(c_12382,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_12618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12382,c_92])).

tff(c_12619,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12715,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12619,c_60])).

tff(c_14480,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14449,c_12715])).

tff(c_15193,plain,(
    ! [A_544,B_545] :
      ( k4_subset_1(u1_struct_0(A_544),B_545,k2_tops_1(A_544,B_545)) = k2_pre_topc(A_544,B_545)
      | ~ m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0(A_544)))
      | ~ l1_pre_topc(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_15201,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_15193])).

tff(c_15212,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_15201])).

tff(c_14975,plain,(
    ! [A_539,B_540] :
      ( r1_tarski(k2_tops_1(A_539,B_540),B_540)
      | ~ v4_pre_topc(B_540,A_539)
      | ~ m1_subset_1(B_540,k1_zfmisc_1(u1_struct_0(A_539)))
      | ~ l1_pre_topc(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_14983,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_14975])).

tff(c_14994,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12619,c_14983])).

tff(c_12700,plain,(
    ! [A_424,B_425] :
      ( r1_tarski(A_424,B_425)
      | ~ m1_subset_1(A_424,k1_zfmisc_1(B_425)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12710,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_12700])).

tff(c_12941,plain,(
    ! [A_442,C_443,B_444] :
      ( r1_tarski(A_442,C_443)
      | ~ r1_tarski(B_444,C_443)
      | ~ r1_tarski(A_442,B_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12970,plain,(
    ! [A_447] :
      ( r1_tarski(A_447,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_447,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12710,c_12941])).

tff(c_12981,plain,(
    ! [A_8,A_447] :
      ( r1_tarski(A_8,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_8,A_447)
      | ~ r1_tarski(A_447,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12970,c_14])).

tff(c_14998,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_14994,c_12981])).

tff(c_15011,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14998])).

tff(c_14813,plain,(
    ! [A_530,B_531,C_532] :
      ( k4_subset_1(A_530,B_531,C_532) = k2_xboole_0(B_531,C_532)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(A_530))
      | ~ m1_subset_1(B_531,k1_zfmisc_1(A_530)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17906,plain,(
    ! [B_618,B_619,A_620] :
      ( k4_subset_1(B_618,B_619,A_620) = k2_xboole_0(B_619,A_620)
      | ~ m1_subset_1(B_619,k1_zfmisc_1(B_618))
      | ~ r1_tarski(A_620,B_618) ) ),
    inference(resolution,[status(thm)],[c_42,c_14813])).

tff(c_18112,plain,(
    ! [A_624] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_624) = k2_xboole_0('#skF_2',A_624)
      | ~ r1_tarski(A_624,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_17906])).

tff(c_18137,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_15011,c_18112])).

tff(c_18188,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15212,c_18137])).

tff(c_12621,plain,(
    ! [A_415,B_416] :
      ( k2_xboole_0(A_415,B_416) = B_416
      | ~ r1_tarski(A_415,B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12649,plain,(
    ! [A_418,B_419] : k2_xboole_0(k4_xboole_0(A_418,B_419),A_418) = A_418 ),
    inference(resolution,[status(thm)],[c_18,c_12621])).

tff(c_12656,plain,(
    ! [B_419] : k4_xboole_0(k1_xboole_0,B_419) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12649,c_12])).

tff(c_12881,plain,(
    ! [A_437,B_438] : k5_xboole_0(A_437,k4_xboole_0(B_438,A_437)) = k2_xboole_0(A_437,B_438) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12893,plain,(
    ! [B_419] : k5_xboole_0(B_419,k1_xboole_0) = k2_xboole_0(B_419,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12656,c_12881])).

tff(c_12896,plain,(
    ! [B_419] : k5_xboole_0(B_419,k1_xboole_0) = B_419 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12893])).

tff(c_13048,plain,(
    ! [A_454,B_455] :
      ( k3_subset_1(A_454,k3_subset_1(A_454,B_455)) = B_455
      | ~ m1_subset_1(B_455,k1_zfmisc_1(A_454)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_13057,plain,(
    ! [B_35,A_34] :
      ( k3_subset_1(B_35,k3_subset_1(B_35,A_34)) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_42,c_13048])).

tff(c_13648,plain,(
    ! [A_483,B_484] :
      ( k4_xboole_0(A_483,B_484) = k3_subset_1(A_483,B_484)
      | ~ m1_subset_1(B_484,k1_zfmisc_1(A_483)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15472,plain,(
    ! [B_554,A_555] :
      ( k4_xboole_0(B_554,A_555) = k3_subset_1(B_554,A_555)
      | ~ r1_tarski(A_555,B_554) ) ),
    inference(resolution,[status(thm)],[c_42,c_13648])).

tff(c_15565,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14994,c_15472])).

tff(c_15588,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_subset_1(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(resolution,[status(thm)],[c_18,c_15472])).

tff(c_13669,plain,(
    ! [A_485] : k4_xboole_0(A_485,k1_xboole_0) = k3_subset_1(A_485,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_13648])).

tff(c_12628,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_18,c_12621])).

tff(c_13719,plain,(
    ! [A_485] : k2_xboole_0(k3_subset_1(A_485,k1_xboole_0),A_485) = A_485 ),
    inference(superposition,[status(thm),theory(equality)],[c_13669,c_12628])).

tff(c_13059,plain,(
    ! [A_33] : k3_subset_1(A_33,k3_subset_1(A_33,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_13048])).

tff(c_13722,plain,(
    ! [A_485] : r1_tarski(k3_subset_1(A_485,k1_xboole_0),A_485) ),
    inference(superposition,[status(thm),theory(equality)],[c_13669,c_18])).

tff(c_15526,plain,(
    ! [A_485] : k4_xboole_0(A_485,k3_subset_1(A_485,k1_xboole_0)) = k3_subset_1(A_485,k3_subset_1(A_485,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_13722,c_15472])).

tff(c_15721,plain,(
    ! [A_557] : k4_xboole_0(A_557,k3_subset_1(A_557,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13059,c_15526])).

tff(c_15793,plain,(
    ! [A_557] : k5_xboole_0(k3_subset_1(A_557,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k3_subset_1(A_557,k1_xboole_0),A_557) ),
    inference(superposition,[status(thm),theory(equality)],[c_15721,c_20])).

tff(c_15837,plain,(
    ! [A_557] : k3_subset_1(A_557,k1_xboole_0) = A_557 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_12896,c_15793])).

tff(c_15867,plain,(
    ! [A_33] : k3_subset_1(A_33,A_33) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15837,c_13059])).

tff(c_13668,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_subset_1(A_20,A_20) ),
    inference(resolution,[status(thm)],[c_67,c_13648])).

tff(c_12681,plain,(
    ! [A_421,B_422] :
      ( k3_xboole_0(A_421,B_422) = A_421
      | ~ r1_tarski(A_421,B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12689,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_12681])).

tff(c_12792,plain,(
    ! [A_431,B_432] : k5_xboole_0(A_431,k3_xboole_0(A_431,B_432)) = k4_xboole_0(A_431,B_432) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12807,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_12689,c_12792])).

tff(c_13784,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13668,c_12807])).

tff(c_16093,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15867,c_13784])).

tff(c_12917,plain,(
    ! [A_440,B_441] : k3_xboole_0(k4_xboole_0(A_440,B_441),A_440) = k4_xboole_0(A_440,B_441) ),
    inference(resolution,[status(thm)],[c_18,c_12681])).

tff(c_12923,plain,(
    ! [A_440,B_441] : k5_xboole_0(k4_xboole_0(A_440,B_441),k4_xboole_0(A_440,B_441)) = k4_xboole_0(k4_xboole_0(A_440,B_441),A_440) ),
    inference(superposition,[status(thm),theory(equality)],[c_12917,c_8])).

tff(c_25162,plain,(
    ! [A_766,B_767] : k4_xboole_0(k4_xboole_0(A_766,B_767),A_766) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16093,c_12923])).

tff(c_25598,plain,(
    ! [A_770,B_771] : k4_xboole_0(k3_subset_1(A_770,k4_xboole_0(A_770,B_771)),A_770) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15588,c_25162])).

tff(c_25777,plain,(
    k4_xboole_0(k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15565,c_25598])).

tff(c_26447,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13057,c_25777])).

tff(c_26487,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14994,c_26447])).

tff(c_26610,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26487,c_20])).

tff(c_26662,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18188,c_12896,c_26610])).

tff(c_48,plain,(
    ! [A_41,B_43] :
      ( k7_subset_1(u1_struct_0(A_41),k2_pre_topc(A_41,B_43),k1_tops_1(A_41,B_43)) = k2_tops_1(A_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26677,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26662,c_48])).

tff(c_26683,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_14449,c_26677])).

tff(c_26685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14480,c_26683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.77/4.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/4.49  
% 10.83/4.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/4.49  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.83/4.49  
% 10.83/4.49  %Foreground sorts:
% 10.83/4.49  
% 10.83/4.49  
% 10.83/4.49  %Background operators:
% 10.83/4.49  
% 10.83/4.49  
% 10.83/4.49  %Foreground operators:
% 10.83/4.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.83/4.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.83/4.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.83/4.49  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.83/4.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.83/4.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.83/4.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.83/4.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.83/4.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.83/4.49  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.83/4.49  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.83/4.49  tff('#skF_2', type, '#skF_2': $i).
% 10.83/4.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.83/4.49  tff('#skF_1', type, '#skF_1': $i).
% 10.83/4.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.83/4.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.83/4.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.83/4.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.83/4.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.83/4.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.83/4.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.83/4.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.83/4.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.83/4.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.83/4.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.83/4.49  
% 10.83/4.52  tff(f_138, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 10.83/4.52  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.83/4.52  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.83/4.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.83/4.52  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.83/4.52  tff(f_89, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.83/4.52  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.83/4.52  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.83/4.52  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.83/4.52  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.83/4.52  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.83/4.52  tff(f_85, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.83/4.52  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.83/4.52  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.83/4.52  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.83/4.52  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.83/4.52  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.83/4.52  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.83/4.52  tff(f_103, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 10.83/4.52  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.83/4.52  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.83/4.52  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.83/4.52  tff(c_14436, plain, (![A_513, B_514, C_515]: (k7_subset_1(A_513, B_514, C_515)=k4_xboole_0(B_514, C_515) | ~m1_subset_1(B_514, k1_zfmisc_1(A_513)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.83/4.52  tff(c_14449, plain, (![C_515]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_515)=k4_xboole_0('#skF_2', C_515))), inference(resolution, [status(thm)], [c_54, c_14436])).
% 10.83/4.52  tff(c_60, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.83/4.52  tff(c_182, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 10.83/4.52  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.83/4.52  tff(c_2479, plain, (![A_183, B_184]: (k4_subset_1(u1_struct_0(A_183), B_184, k2_tops_1(A_183, B_184))=k2_pre_topc(A_183, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.83/4.52  tff(c_2487, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_2479])).
% 10.83/4.52  tff(c_2498, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2487])).
% 10.83/4.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.83/4.52  tff(c_1754, plain, (![A_154, B_155, C_156]: (k7_subset_1(A_154, B_155, C_156)=k4_xboole_0(B_155, C_156) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.83/4.52  tff(c_1816, plain, (![C_161]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_161)=k4_xboole_0('#skF_2', C_161))), inference(resolution, [status(thm)], [c_54, c_1754])).
% 10.83/4.52  tff(c_66, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.83/4.52  tff(c_92, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 10.83/4.52  tff(c_1822, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1816, c_92])).
% 10.83/4.52  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.83/4.52  tff(c_2125, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1822, c_18])).
% 10.83/4.52  tff(c_155, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.83/4.52  tff(c_169, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_155])).
% 10.83/4.52  tff(c_416, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, C_86) | ~r1_tarski(B_87, C_86) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.83/4.52  tff(c_445, plain, (![A_90]: (r1_tarski(A_90, u1_struct_0('#skF_1')) | ~r1_tarski(A_90, '#skF_2'))), inference(resolution, [status(thm)], [c_169, c_416])).
% 10.83/4.52  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.83/4.52  tff(c_456, plain, (![A_8, A_90]: (r1_tarski(A_8, u1_struct_0('#skF_1')) | ~r1_tarski(A_8, A_90) | ~r1_tarski(A_90, '#skF_2'))), inference(resolution, [status(thm)], [c_445, c_14])).
% 10.83/4.52  tff(c_2134, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2125, c_456])).
% 10.83/4.52  tff(c_2147, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2134])).
% 10.83/4.52  tff(c_42, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.83/4.52  tff(c_2176, plain, (![A_171, B_172, C_173]: (k4_subset_1(A_171, B_172, C_173)=k2_xboole_0(B_172, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | ~m1_subset_1(B_172, k1_zfmisc_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.83/4.52  tff(c_5330, plain, (![B_261, B_262, A_263]: (k4_subset_1(B_261, B_262, A_263)=k2_xboole_0(B_262, A_263) | ~m1_subset_1(B_262, k1_zfmisc_1(B_261)) | ~r1_tarski(A_263, B_261))), inference(resolution, [status(thm)], [c_42, c_2176])).
% 10.83/4.52  tff(c_5575, plain, (![A_269]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_269)=k2_xboole_0('#skF_2', A_269) | ~r1_tarski(A_269, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_5330])).
% 10.83/4.52  tff(c_5605, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2147, c_5575])).
% 10.83/4.52  tff(c_5649, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_5605])).
% 10.83/4.52  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.83/4.52  tff(c_93, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.83/4.52  tff(c_121, plain, (![A_61, B_62]: (k2_xboole_0(k4_xboole_0(A_61, B_62), A_61)=A_61)), inference(resolution, [status(thm)], [c_18, c_93])).
% 10.83/4.52  tff(c_128, plain, (![B_62]: (k4_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_121, c_12])).
% 10.83/4.52  tff(c_343, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.83/4.52  tff(c_352, plain, (![B_62]: (k5_xboole_0(B_62, k1_xboole_0)=k2_xboole_0(B_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_343])).
% 10.83/4.52  tff(c_355, plain, (![B_62]: (k5_xboole_0(B_62, k1_xboole_0)=B_62)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_352])).
% 10.83/4.52  tff(c_38, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.83/4.52  tff(c_966, plain, (![A_130, B_131]: (k4_xboole_0(A_130, B_131)=k3_subset_1(A_130, B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.83/4.52  tff(c_983, plain, (![A_132]: (k4_xboole_0(A_132, k1_xboole_0)=k3_subset_1(A_132, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_966])).
% 10.83/4.52  tff(c_100, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), A_13)=A_13)), inference(resolution, [status(thm)], [c_18, c_93])).
% 10.83/4.52  tff(c_1033, plain, (![A_132]: (k2_xboole_0(k3_subset_1(A_132, k1_xboole_0), A_132)=A_132)), inference(superposition, [status(thm), theory('equality')], [c_983, c_100])).
% 10.83/4.52  tff(c_742, plain, (![A_119, B_120]: (k3_subset_1(A_119, k3_subset_1(A_119, B_120))=B_120 | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.83/4.52  tff(c_753, plain, (![A_33]: (k3_subset_1(A_33, k3_subset_1(A_33, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_742])).
% 10.83/4.52  tff(c_1036, plain, (![A_132]: (r1_tarski(k3_subset_1(A_132, k1_xboole_0), A_132))), inference(superposition, [status(thm), theory('equality')], [c_983, c_18])).
% 10.83/4.52  tff(c_2985, plain, (![B_201, A_202]: (k4_xboole_0(B_201, A_202)=k3_subset_1(B_201, A_202) | ~r1_tarski(A_202, B_201))), inference(resolution, [status(thm)], [c_42, c_966])).
% 10.83/4.52  tff(c_3039, plain, (![A_132]: (k4_xboole_0(A_132, k3_subset_1(A_132, k1_xboole_0))=k3_subset_1(A_132, k3_subset_1(A_132, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1036, c_2985])).
% 10.83/4.52  tff(c_3226, plain, (![A_204]: (k4_xboole_0(A_204, k3_subset_1(A_204, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_753, c_3039])).
% 10.83/4.52  tff(c_20, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.83/4.52  tff(c_3298, plain, (![A_204]: (k5_xboole_0(k3_subset_1(A_204, k1_xboole_0), k1_xboole_0)=k2_xboole_0(k3_subset_1(A_204, k1_xboole_0), A_204))), inference(superposition, [status(thm), theory('equality')], [c_3226, c_20])).
% 10.83/4.52  tff(c_3342, plain, (![A_204]: (k3_subset_1(A_204, k1_xboole_0)=A_204)), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_355, c_3298])).
% 10.83/4.52  tff(c_3372, plain, (![A_33]: (k3_subset_1(A_33, A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_753])).
% 10.83/4.52  tff(c_22, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.83/4.52  tff(c_26, plain, (![A_20]: (m1_subset_1(k2_subset_1(A_20), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.83/4.52  tff(c_67, plain, (![A_20]: (m1_subset_1(A_20, k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 10.83/4.52  tff(c_982, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_subset_1(A_20, A_20))), inference(resolution, [status(thm)], [c_67, c_966])).
% 10.83/4.52  tff(c_216, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.83/4.52  tff(c_232, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_216])).
% 10.83/4.52  tff(c_303, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.83/4.52  tff(c_318, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_232, c_303])).
% 10.83/4.52  tff(c_1152, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_982, c_318])).
% 10.83/4.52  tff(c_3625, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3372, c_1152])).
% 10.83/4.52  tff(c_392, plain, (![A_83, B_84]: (k3_xboole_0(k4_xboole_0(A_83, B_84), A_83)=k4_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_18, c_216])).
% 10.83/4.52  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.83/4.52  tff(c_398, plain, (![A_83, B_84]: (k5_xboole_0(k4_xboole_0(A_83, B_84), k4_xboole_0(A_83, B_84))=k4_xboole_0(k4_xboole_0(A_83, B_84), A_83))), inference(superposition, [status(thm), theory('equality')], [c_392, c_8])).
% 10.83/4.52  tff(c_11814, plain, (![A_392, B_393]: (k4_xboole_0(k4_xboole_0(A_392, B_393), A_392)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3625, c_398])).
% 10.83/4.52  tff(c_12038, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1822, c_11814])).
% 10.83/4.52  tff(c_12325, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12038, c_20])).
% 10.83/4.52  tff(c_12372, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5649, c_355, c_12325])).
% 10.83/4.52  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.83/4.52  tff(c_1966, plain, (![A_166, B_167]: (v4_pre_topc(k2_pre_topc(A_166, B_167), A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.83/4.52  tff(c_1974, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1966])).
% 10.83/4.52  tff(c_1985, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1974])).
% 10.83/4.52  tff(c_12379, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12372, c_1985])).
% 10.83/4.52  tff(c_12381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_12379])).
% 10.83/4.52  tff(c_12382, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 10.83/4.52  tff(c_12618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12382, c_92])).
% 10.83/4.52  tff(c_12619, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 10.83/4.52  tff(c_12715, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12619, c_60])).
% 10.83/4.52  tff(c_14480, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14449, c_12715])).
% 10.83/4.52  tff(c_15193, plain, (![A_544, B_545]: (k4_subset_1(u1_struct_0(A_544), B_545, k2_tops_1(A_544, B_545))=k2_pre_topc(A_544, B_545) | ~m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0(A_544))) | ~l1_pre_topc(A_544))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.83/4.52  tff(c_15201, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_15193])).
% 10.83/4.52  tff(c_15212, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_15201])).
% 10.83/4.52  tff(c_14975, plain, (![A_539, B_540]: (r1_tarski(k2_tops_1(A_539, B_540), B_540) | ~v4_pre_topc(B_540, A_539) | ~m1_subset_1(B_540, k1_zfmisc_1(u1_struct_0(A_539))) | ~l1_pre_topc(A_539))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.83/4.52  tff(c_14983, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_14975])).
% 10.83/4.52  tff(c_14994, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12619, c_14983])).
% 10.83/4.52  tff(c_12700, plain, (![A_424, B_425]: (r1_tarski(A_424, B_425) | ~m1_subset_1(A_424, k1_zfmisc_1(B_425)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.83/4.52  tff(c_12710, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_12700])).
% 10.83/4.52  tff(c_12941, plain, (![A_442, C_443, B_444]: (r1_tarski(A_442, C_443) | ~r1_tarski(B_444, C_443) | ~r1_tarski(A_442, B_444))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.83/4.52  tff(c_12970, plain, (![A_447]: (r1_tarski(A_447, u1_struct_0('#skF_1')) | ~r1_tarski(A_447, '#skF_2'))), inference(resolution, [status(thm)], [c_12710, c_12941])).
% 10.83/4.52  tff(c_12981, plain, (![A_8, A_447]: (r1_tarski(A_8, u1_struct_0('#skF_1')) | ~r1_tarski(A_8, A_447) | ~r1_tarski(A_447, '#skF_2'))), inference(resolution, [status(thm)], [c_12970, c_14])).
% 10.83/4.52  tff(c_14998, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_14994, c_12981])).
% 10.83/4.52  tff(c_15011, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14998])).
% 10.83/4.52  tff(c_14813, plain, (![A_530, B_531, C_532]: (k4_subset_1(A_530, B_531, C_532)=k2_xboole_0(B_531, C_532) | ~m1_subset_1(C_532, k1_zfmisc_1(A_530)) | ~m1_subset_1(B_531, k1_zfmisc_1(A_530)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.83/4.52  tff(c_17906, plain, (![B_618, B_619, A_620]: (k4_subset_1(B_618, B_619, A_620)=k2_xboole_0(B_619, A_620) | ~m1_subset_1(B_619, k1_zfmisc_1(B_618)) | ~r1_tarski(A_620, B_618))), inference(resolution, [status(thm)], [c_42, c_14813])).
% 10.83/4.52  tff(c_18112, plain, (![A_624]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_624)=k2_xboole_0('#skF_2', A_624) | ~r1_tarski(A_624, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_17906])).
% 10.83/4.52  tff(c_18137, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_15011, c_18112])).
% 10.83/4.52  tff(c_18188, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15212, c_18137])).
% 10.83/4.52  tff(c_12621, plain, (![A_415, B_416]: (k2_xboole_0(A_415, B_416)=B_416 | ~r1_tarski(A_415, B_416))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.83/4.52  tff(c_12649, plain, (![A_418, B_419]: (k2_xboole_0(k4_xboole_0(A_418, B_419), A_418)=A_418)), inference(resolution, [status(thm)], [c_18, c_12621])).
% 10.83/4.52  tff(c_12656, plain, (![B_419]: (k4_xboole_0(k1_xboole_0, B_419)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12649, c_12])).
% 10.83/4.52  tff(c_12881, plain, (![A_437, B_438]: (k5_xboole_0(A_437, k4_xboole_0(B_438, A_437))=k2_xboole_0(A_437, B_438))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.83/4.52  tff(c_12893, plain, (![B_419]: (k5_xboole_0(B_419, k1_xboole_0)=k2_xboole_0(B_419, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12656, c_12881])).
% 10.83/4.52  tff(c_12896, plain, (![B_419]: (k5_xboole_0(B_419, k1_xboole_0)=B_419)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12893])).
% 10.83/4.52  tff(c_13048, plain, (![A_454, B_455]: (k3_subset_1(A_454, k3_subset_1(A_454, B_455))=B_455 | ~m1_subset_1(B_455, k1_zfmisc_1(A_454)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.83/4.52  tff(c_13057, plain, (![B_35, A_34]: (k3_subset_1(B_35, k3_subset_1(B_35, A_34))=A_34 | ~r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_42, c_13048])).
% 10.83/4.52  tff(c_13648, plain, (![A_483, B_484]: (k4_xboole_0(A_483, B_484)=k3_subset_1(A_483, B_484) | ~m1_subset_1(B_484, k1_zfmisc_1(A_483)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.83/4.52  tff(c_15472, plain, (![B_554, A_555]: (k4_xboole_0(B_554, A_555)=k3_subset_1(B_554, A_555) | ~r1_tarski(A_555, B_554))), inference(resolution, [status(thm)], [c_42, c_13648])).
% 10.83/4.52  tff(c_15565, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14994, c_15472])).
% 10.83/4.52  tff(c_15588, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_subset_1(A_13, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_18, c_15472])).
% 10.83/4.52  tff(c_13669, plain, (![A_485]: (k4_xboole_0(A_485, k1_xboole_0)=k3_subset_1(A_485, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_13648])).
% 10.83/4.52  tff(c_12628, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), A_13)=A_13)), inference(resolution, [status(thm)], [c_18, c_12621])).
% 10.83/4.52  tff(c_13719, plain, (![A_485]: (k2_xboole_0(k3_subset_1(A_485, k1_xboole_0), A_485)=A_485)), inference(superposition, [status(thm), theory('equality')], [c_13669, c_12628])).
% 10.83/4.52  tff(c_13059, plain, (![A_33]: (k3_subset_1(A_33, k3_subset_1(A_33, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_13048])).
% 10.83/4.52  tff(c_13722, plain, (![A_485]: (r1_tarski(k3_subset_1(A_485, k1_xboole_0), A_485))), inference(superposition, [status(thm), theory('equality')], [c_13669, c_18])).
% 10.83/4.52  tff(c_15526, plain, (![A_485]: (k4_xboole_0(A_485, k3_subset_1(A_485, k1_xboole_0))=k3_subset_1(A_485, k3_subset_1(A_485, k1_xboole_0)))), inference(resolution, [status(thm)], [c_13722, c_15472])).
% 10.83/4.52  tff(c_15721, plain, (![A_557]: (k4_xboole_0(A_557, k3_subset_1(A_557, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13059, c_15526])).
% 10.83/4.52  tff(c_15793, plain, (![A_557]: (k5_xboole_0(k3_subset_1(A_557, k1_xboole_0), k1_xboole_0)=k2_xboole_0(k3_subset_1(A_557, k1_xboole_0), A_557))), inference(superposition, [status(thm), theory('equality')], [c_15721, c_20])).
% 10.83/4.52  tff(c_15837, plain, (![A_557]: (k3_subset_1(A_557, k1_xboole_0)=A_557)), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_12896, c_15793])).
% 10.83/4.52  tff(c_15867, plain, (![A_33]: (k3_subset_1(A_33, A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15837, c_13059])).
% 10.83/4.52  tff(c_13668, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_subset_1(A_20, A_20))), inference(resolution, [status(thm)], [c_67, c_13648])).
% 10.83/4.52  tff(c_12681, plain, (![A_421, B_422]: (k3_xboole_0(A_421, B_422)=A_421 | ~r1_tarski(A_421, B_422))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.83/4.52  tff(c_12689, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_12681])).
% 10.83/4.52  tff(c_12792, plain, (![A_431, B_432]: (k5_xboole_0(A_431, k3_xboole_0(A_431, B_432))=k4_xboole_0(A_431, B_432))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.83/4.52  tff(c_12807, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_12689, c_12792])).
% 10.83/4.52  tff(c_13784, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_13668, c_12807])).
% 10.83/4.52  tff(c_16093, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15867, c_13784])).
% 10.83/4.52  tff(c_12917, plain, (![A_440, B_441]: (k3_xboole_0(k4_xboole_0(A_440, B_441), A_440)=k4_xboole_0(A_440, B_441))), inference(resolution, [status(thm)], [c_18, c_12681])).
% 10.83/4.52  tff(c_12923, plain, (![A_440, B_441]: (k5_xboole_0(k4_xboole_0(A_440, B_441), k4_xboole_0(A_440, B_441))=k4_xboole_0(k4_xboole_0(A_440, B_441), A_440))), inference(superposition, [status(thm), theory('equality')], [c_12917, c_8])).
% 10.83/4.52  tff(c_25162, plain, (![A_766, B_767]: (k4_xboole_0(k4_xboole_0(A_766, B_767), A_766)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16093, c_12923])).
% 10.83/4.52  tff(c_25598, plain, (![A_770, B_771]: (k4_xboole_0(k3_subset_1(A_770, k4_xboole_0(A_770, B_771)), A_770)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15588, c_25162])).
% 10.83/4.52  tff(c_25777, plain, (k4_xboole_0(k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15565, c_25598])).
% 10.83/4.52  tff(c_26447, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0 | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13057, c_25777])).
% 10.83/4.52  tff(c_26487, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14994, c_26447])).
% 10.83/4.52  tff(c_26610, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26487, c_20])).
% 10.83/4.52  tff(c_26662, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18188, c_12896, c_26610])).
% 10.83/4.52  tff(c_48, plain, (![A_41, B_43]: (k7_subset_1(u1_struct_0(A_41), k2_pre_topc(A_41, B_43), k1_tops_1(A_41, B_43))=k2_tops_1(A_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.83/4.52  tff(c_26677, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26662, c_48])).
% 10.83/4.52  tff(c_26683, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_14449, c_26677])).
% 10.83/4.52  tff(c_26685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14480, c_26683])).
% 10.83/4.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.83/4.52  
% 10.83/4.52  Inference rules
% 10.83/4.52  ----------------------
% 10.83/4.52  #Ref     : 0
% 10.83/4.52  #Sup     : 6215
% 10.83/4.52  #Fact    : 0
% 10.83/4.52  #Define  : 0
% 10.83/4.52  #Split   : 7
% 10.83/4.52  #Chain   : 0
% 10.83/4.52  #Close   : 0
% 10.83/4.52  
% 10.83/4.52  Ordering : KBO
% 10.83/4.52  
% 10.83/4.52  Simplification rules
% 10.83/4.52  ----------------------
% 10.83/4.52  #Subsume      : 499
% 10.83/4.52  #Demod        : 5744
% 10.83/4.52  #Tautology    : 3870
% 10.83/4.52  #SimpNegUnit  : 3
% 10.83/4.52  #BackRed      : 96
% 10.83/4.52  
% 10.83/4.52  #Partial instantiations: 0
% 10.83/4.52  #Strategies tried      : 1
% 10.83/4.52  
% 10.83/4.52  Timing (in seconds)
% 10.83/4.52  ----------------------
% 10.83/4.52  Preprocessing        : 0.35
% 10.83/4.52  Parsing              : 0.19
% 10.83/4.52  CNF conversion       : 0.02
% 10.83/4.52  Main loop            : 3.39
% 10.83/4.52  Inferencing          : 0.84
% 10.83/4.52  Reduction            : 1.50
% 10.83/4.52  Demodulation         : 1.20
% 10.83/4.52  BG Simplification    : 0.08
% 10.83/4.52  Subsumption          : 0.71
% 10.83/4.52  Abstraction          : 0.13
% 10.83/4.52  MUC search           : 0.00
% 10.83/4.52  Cooper               : 0.00
% 10.83/4.52  Total                : 3.80
% 10.83/4.52  Index Insertion      : 0.00
% 10.83/4.52  Index Deletion       : 0.00
% 10.83/4.52  Index Matching       : 0.00
% 10.83/4.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
