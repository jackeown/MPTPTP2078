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
% DateTime   : Thu Dec  3 10:22:27 EST 2020

% Result     : Theorem 35.27s
% Output     : CNFRefutation 35.31s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 772 expanded)
%              Number of leaves         :   36 ( 279 expanded)
%              Depth                    :   20
%              Number of atoms          :  291 (2207 expanded)
%              Number of equality atoms :   43 ( 329 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tops_1 > v4_pre_topc > v3_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => k1_tops_1(A,k2_tops_1(A,B)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => ( v3_tops_1(B,A)
            <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_42,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( r1_tarski(B_16,k2_pre_topc(A_14,k1_tops_1(A_14,B_16)))
      | ~ v4_tops_1(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( k1_tops_1(A_60,k1_tops_1(A_60,B_61)) = k1_tops_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_144,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_136])).

tff(c_150,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_144])).

tff(c_102,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_tops_1(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( v4_pre_topc(k2_tops_1(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_160,plain,(
    ! [A_62,B_63] :
      ( v4_pre_topc(k2_tops_1(A_62,k1_tops_1(A_62,B_63)),A_62)
      | ~ v2_pre_topc(A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_102,c_24])).

tff(c_163,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_160])).

tff(c_165,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_163])).

tff(c_166,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_169,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_169])).

tff(c_175,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_60,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tops_1(A_46,B_47),B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_65,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_12,plain,(
    ! [A_7,B_11,C_13] :
      ( r1_tarski(k2_pre_topc(A_7,B_11),k2_pre_topc(A_7,C_13))
      | ~ r1_tarski(B_11,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_pre_topc(A_5,k2_pre_topc(A_5,B_6)) = k2_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_10])).

tff(c_216,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_201])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k2_pre_topc(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [A_80,B_81] :
      ( v4_pre_topc(k2_tops_1(A_80,k2_pre_topc(A_80,B_81)),A_80)
      | ~ v2_pre_topc(A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_92,c_24])).

tff(c_313,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_310])).

tff(c_318,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_313])).

tff(c_4899,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_4902,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_4899])).

tff(c_4906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_175,c_4902])).

tff(c_4908,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_112,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,k2_pre_topc(A_58,B_59)) = k2_pre_topc(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_112])).

tff(c_126,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_120])).

tff(c_316,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_310])).

tff(c_320,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_316])).

tff(c_321,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_324,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_321])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_324])).

tff(c_330,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_1407,plain,(
    ! [A_97,B_98,C_99] :
      ( r1_tarski(k2_pre_topc(A_97,B_98),k2_pre_topc(A_97,C_99))
      | ~ r1_tarski(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1427,plain,(
    ! [B_98] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_98),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_98,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_1407])).

tff(c_1440,plain,(
    ! [B_98] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_98),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_98,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_330,c_1427])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6486,plain,(
    ! [A_155,C_156,B_157] :
      ( k2_pre_topc(A_155,C_156) = k2_pre_topc(A_155,B_157)
      | ~ r1_tarski(k2_pre_topc(A_155,C_156),k2_pre_topc(A_155,B_157))
      | ~ r1_tarski(B_157,C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_1407,c_2])).

tff(c_6513,plain,(
    ! [B_98] :
      ( k2_pre_topc('#skF_1',B_98) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_98)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_98,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1440,c_6486])).

tff(c_7121,plain,(
    ! [B_161] :
      ( k2_pre_topc('#skF_1',B_161) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_161)
      | ~ r1_tarski(B_161,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6513])).

tff(c_7136,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4908,c_7121])).

tff(c_7191,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_7136])).

tff(c_76485,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7191])).

tff(c_76790,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_76485])).

tff(c_76797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_175,c_46,c_65,c_76790])).

tff(c_76798,plain,
    ( ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_7191])).

tff(c_76836,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_76798])).

tff(c_77186,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_76836])).

tff(c_77190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_77186])).

tff(c_77191,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76798])).

tff(c_1242,plain,(
    ! [A_95,B_96] :
      ( k7_subset_1(u1_struct_0(A_95),k2_pre_topc(A_95,B_96),k1_tops_1(A_95,B_96)) = k2_tops_1(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1275,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_1242])).

tff(c_1298,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_175,c_1275])).

tff(c_77231,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77191,c_1298])).

tff(c_28,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_77809,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_77231,c_28])).

tff(c_77816,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_77809])).

tff(c_174,plain,(
    v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_83,plain,(
    ! [A_52,B_53] :
      ( v3_pre_topc(k1_tops_1(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_87,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_91,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_87])).

tff(c_485,plain,(
    ! [A_84,B_85] :
      ( v3_tops_1(k2_tops_1(A_84,B_85),A_84)
      | ~ v3_pre_topc(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_489,plain,
    ( v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_485])).

tff(c_503,plain,(
    v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_91,c_489])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2148,plain,(
    ! [A_108,B_109] :
      ( k1_tops_1(A_108,k1_tops_1(A_108,k2_tops_1(A_108,B_109))) = k1_tops_1(A_108,k2_tops_1(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_2162,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_2148])).

tff(c_2191,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2162])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( v3_pre_topc(k1_tops_1(A_23,B_24),A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_109,plain,(
    ! [A_56,B_57] :
      ( v3_pre_topc(k1_tops_1(A_56,k1_tops_1(A_56,B_57)),A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_102,c_26])).

tff(c_2424,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2191,c_109])).

tff(c_2451,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_2424])).

tff(c_3531,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2451])).

tff(c_3534,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_3531])).

tff(c_3538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_175,c_3534])).

tff(c_3540,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2451])).

tff(c_38,plain,(
    ! [A_36,B_38] :
      ( k2_tops_1(A_36,B_38) = B_38
      | ~ v3_tops_1(B_38,A_36)
      | ~ v4_pre_topc(B_38,A_36)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3553,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3540,c_38])).

tff(c_3588,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_174,c_503,c_3553])).

tff(c_365,plain,(
    ! [A_82,B_83] :
      ( k1_tops_1(A_82,k2_tops_1(A_82,k2_tops_1(A_82,B_83))) = k1_xboole_0
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_369,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_365])).

tff(c_383,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_369])).

tff(c_3687,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3588,c_383])).

tff(c_77836,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77816,c_3687])).

tff(c_77851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_77836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.27/24.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.31/24.97  
% 35.31/24.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.31/24.97  %$ v4_tops_1 > v4_pre_topc > v3_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 35.31/24.97  
% 35.31/24.97  %Foreground sorts:
% 35.31/24.97  
% 35.31/24.97  
% 35.31/24.97  %Background operators:
% 35.31/24.97  
% 35.31/24.97  
% 35.31/24.97  %Foreground operators:
% 35.31/24.97  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 35.31/24.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.31/24.97  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 35.31/24.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 35.31/24.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 35.31/24.97  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 35.31/24.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 35.31/24.97  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 35.31/24.97  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 35.31/24.97  tff('#skF_2', type, '#skF_2': $i).
% 35.31/24.97  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 35.31/24.97  tff('#skF_1', type, '#skF_1': $i).
% 35.31/24.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 35.31/24.97  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 35.31/24.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.31/24.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.31/24.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 35.31/24.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 35.31/24.97  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 35.31/24.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 35.31/24.97  
% 35.31/25.00  tff(f_157, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (k1_tops_1(A, k2_tops_1(A, B)) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_tops_1)).
% 35.31/25.00  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 35.31/25.00  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 35.31/25.00  tff(f_116, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 35.31/25.00  tff(f_86, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_tops_1)).
% 35.31/25.00  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 35.31/25.00  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 35.31/25.00  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 35.31/25.00  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 35.31/25.00  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 35.31/25.00  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 35.31/25.00  tff(f_94, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 35.31/25.00  tff(f_145, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tops_1)).
% 35.31/25.00  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 35.31/25.00  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 35.31/25.00  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 35.31/25.00  tff(c_42, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_157])).
% 35.31/25.00  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 35.31/25.00  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 35.31/25.00  tff(c_44, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 35.31/25.00  tff(c_16, plain, (![B_16, A_14]: (r1_tarski(B_16, k2_pre_topc(A_14, k1_tops_1(A_14, B_16))) | ~v4_tops_1(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 35.31/25.00  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 35.31/25.00  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 35.31/25.00  tff(c_136, plain, (![A_60, B_61]: (k1_tops_1(A_60, k1_tops_1(A_60, B_61))=k1_tops_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_116])).
% 35.31/25.00  tff(c_144, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_136])).
% 35.31/25.00  tff(c_150, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_144])).
% 35.31/25.00  tff(c_102, plain, (![A_56, B_57]: (m1_subset_1(k1_tops_1(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_72])).
% 35.31/25.00  tff(c_24, plain, (![A_21, B_22]: (v4_pre_topc(k2_tops_1(A_21, B_22), A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 35.31/25.00  tff(c_160, plain, (![A_62, B_63]: (v4_pre_topc(k2_tops_1(A_62, k1_tops_1(A_62, B_63)), A_62) | ~v2_pre_topc(A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_102, c_24])).
% 35.31/25.00  tff(c_163, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_150, c_160])).
% 35.31/25.00  tff(c_165, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_163])).
% 35.31/25.00  tff(c_166, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_165])).
% 35.31/25.00  tff(c_169, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_166])).
% 35.31/25.00  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_169])).
% 35.31/25.00  tff(c_175, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_165])).
% 35.31/25.00  tff(c_60, plain, (![A_46, B_47]: (r1_tarski(k1_tops_1(A_46, B_47), B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.31/25.00  tff(c_62, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_60])).
% 35.31/25.00  tff(c_65, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 35.31/25.00  tff(c_12, plain, (![A_7, B_11, C_13]: (r1_tarski(k2_pre_topc(A_7, B_11), k2_pre_topc(A_7, C_13)) | ~r1_tarski(B_11, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 35.31/25.00  tff(c_10, plain, (![A_5, B_6]: (k2_pre_topc(A_5, k2_pre_topc(A_5, B_6))=k2_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 35.31/25.00  tff(c_201, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_175, c_10])).
% 35.31/25.00  tff(c_216, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_201])).
% 35.31/25.00  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.31/25.00  tff(c_92, plain, (![A_54, B_55]: (m1_subset_1(k2_pre_topc(A_54, B_55), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.31/25.00  tff(c_310, plain, (![A_80, B_81]: (v4_pre_topc(k2_tops_1(A_80, k2_pre_topc(A_80, B_81)), A_80) | ~v2_pre_topc(A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_92, c_24])).
% 35.31/25.00  tff(c_313, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_216, c_310])).
% 35.31/25.00  tff(c_318, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_313])).
% 35.31/25.00  tff(c_4899, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_318])).
% 35.31/25.00  tff(c_4902, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_4899])).
% 35.31/25.00  tff(c_4906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_175, c_4902])).
% 35.31/25.00  tff(c_4908, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_318])).
% 35.31/25.00  tff(c_112, plain, (![A_58, B_59]: (k2_pre_topc(A_58, k2_pre_topc(A_58, B_59))=k2_pre_topc(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 35.31/25.00  tff(c_120, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_112])).
% 35.31/25.00  tff(c_126, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_120])).
% 35.31/25.00  tff(c_316, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_126, c_310])).
% 35.31/25.00  tff(c_320, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_316])).
% 35.31/25.00  tff(c_321, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_320])).
% 35.31/25.00  tff(c_324, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_321])).
% 35.31/25.00  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_324])).
% 35.31/25.00  tff(c_330, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_320])).
% 35.31/25.00  tff(c_1407, plain, (![A_97, B_98, C_99]: (r1_tarski(k2_pre_topc(A_97, B_98), k2_pre_topc(A_97, C_99)) | ~r1_tarski(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_55])).
% 35.31/25.00  tff(c_1427, plain, (![B_98]: (r1_tarski(k2_pre_topc('#skF_1', B_98), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_98, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_1407])).
% 35.31/25.00  tff(c_1440, plain, (![B_98]: (r1_tarski(k2_pre_topc('#skF_1', B_98), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_98, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_330, c_1427])).
% 35.31/25.00  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 35.31/25.00  tff(c_6486, plain, (![A_155, C_156, B_157]: (k2_pre_topc(A_155, C_156)=k2_pre_topc(A_155, B_157) | ~r1_tarski(k2_pre_topc(A_155, C_156), k2_pre_topc(A_155, B_157)) | ~r1_tarski(B_157, C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(resolution, [status(thm)], [c_1407, c_2])).
% 35.31/25.00  tff(c_6513, plain, (![B_98]: (k2_pre_topc('#skF_1', B_98)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_98) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_98, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1440, c_6486])).
% 35.31/25.00  tff(c_7121, plain, (![B_161]: (k2_pre_topc('#skF_1', B_161)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_161) | ~r1_tarski(B_161, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_6513])).
% 35.31/25.00  tff(c_7136, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4908, c_7121])).
% 35.31/25.00  tff(c_7191, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_7136])).
% 35.31/25.00  tff(c_76485, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7191])).
% 35.31/25.00  tff(c_76790, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_76485])).
% 35.31/25.00  tff(c_76797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_175, c_46, c_65, c_76790])).
% 35.31/25.00  tff(c_76798, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_7191])).
% 35.31/25.00  tff(c_76836, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_76798])).
% 35.31/25.00  tff(c_77186, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_76836])).
% 35.31/25.00  tff(c_77190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_77186])).
% 35.31/25.00  tff(c_77191, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_76798])).
% 35.31/25.00  tff(c_1242, plain, (![A_95, B_96]: (k7_subset_1(u1_struct_0(A_95), k2_pre_topc(A_95, B_96), k1_tops_1(A_95, B_96))=k2_tops_1(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_101])).
% 35.31/25.00  tff(c_1275, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_150, c_1242])).
% 35.31/25.00  tff(c_1298, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_175, c_1275])).
% 35.31/25.00  tff(c_77231, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77191, c_1298])).
% 35.31/25.00  tff(c_28, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 35.31/25.00  tff(c_77809, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_77231, c_28])).
% 35.31/25.00  tff(c_77816, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_77809])).
% 35.31/25.00  tff(c_174, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_165])).
% 35.31/25.00  tff(c_83, plain, (![A_52, B_53]: (v3_pre_topc(k1_tops_1(A_52, B_53), A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_94])).
% 35.31/25.00  tff(c_87, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_83])).
% 35.31/25.00  tff(c_91, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_87])).
% 35.31/25.00  tff(c_485, plain, (![A_84, B_85]: (v3_tops_1(k2_tops_1(A_84, B_85), A_84) | ~v3_pre_topc(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_145])).
% 35.31/25.00  tff(c_489, plain, (v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_175, c_485])).
% 35.31/25.00  tff(c_503, plain, (v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_91, c_489])).
% 35.31/25.00  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 35.31/25.00  tff(c_2148, plain, (![A_108, B_109]: (k1_tops_1(A_108, k1_tops_1(A_108, k2_tops_1(A_108, B_109)))=k1_tops_1(A_108, k2_tops_1(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_22, c_136])).
% 35.31/25.00  tff(c_2162, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_175, c_2148])).
% 35.31/25.00  tff(c_2191, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2162])).
% 35.31/25.00  tff(c_26, plain, (![A_23, B_24]: (v3_pre_topc(k1_tops_1(A_23, B_24), A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 35.31/25.00  tff(c_109, plain, (![A_56, B_57]: (v3_pre_topc(k1_tops_1(A_56, k1_tops_1(A_56, B_57)), A_56) | ~v2_pre_topc(A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_102, c_26])).
% 35.31/25.00  tff(c_2424, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2191, c_109])).
% 35.31/25.00  tff(c_2451, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_2424])).
% 35.31/25.00  tff(c_3531, plain, (~m1_subset_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2451])).
% 35.31/25.00  tff(c_3534, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_3531])).
% 35.31/25.00  tff(c_3538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_175, c_3534])).
% 35.31/25.00  tff(c_3540, plain, (m1_subset_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2451])).
% 35.31/25.00  tff(c_38, plain, (![A_36, B_38]: (k2_tops_1(A_36, B_38)=B_38 | ~v3_tops_1(B_38, A_36) | ~v4_pre_topc(B_38, A_36) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_134])).
% 35.31/25.00  tff(c_3553, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3540, c_38])).
% 35.31/25.00  tff(c_3588, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_174, c_503, c_3553])).
% 35.31/25.00  tff(c_365, plain, (![A_82, B_83]: (k1_tops_1(A_82, k2_tops_1(A_82, k2_tops_1(A_82, B_83)))=k1_xboole_0 | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_110])).
% 35.31/25.00  tff(c_369, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_175, c_365])).
% 35.31/25.00  tff(c_383, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_369])).
% 35.31/25.00  tff(c_3687, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3588, c_383])).
% 35.31/25.00  tff(c_77836, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77816, c_3687])).
% 35.31/25.00  tff(c_77851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_77836])).
% 35.31/25.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.31/25.00  
% 35.31/25.00  Inference rules
% 35.31/25.00  ----------------------
% 35.31/25.00  #Ref     : 0
% 35.31/25.00  #Sup     : 16991
% 35.31/25.00  #Fact    : 0
% 35.31/25.00  #Define  : 0
% 35.31/25.00  #Split   : 258
% 35.31/25.00  #Chain   : 0
% 35.31/25.00  #Close   : 0
% 35.31/25.00  
% 35.31/25.00  Ordering : KBO
% 35.31/25.00  
% 35.31/25.00  Simplification rules
% 35.31/25.00  ----------------------
% 35.31/25.00  #Subsume      : 3160
% 35.31/25.00  #Demod        : 61751
% 35.31/25.00  #Tautology    : 7230
% 35.31/25.00  #SimpNegUnit  : 54
% 35.31/25.00  #BackRed      : 179
% 35.31/25.00  
% 35.31/25.00  #Partial instantiations: 0
% 35.31/25.00  #Strategies tried      : 1
% 35.31/25.00  
% 35.31/25.00  Timing (in seconds)
% 35.31/25.00  ----------------------
% 35.31/25.00  Preprocessing        : 0.34
% 35.31/25.00  Parsing              : 0.19
% 35.31/25.00  CNF conversion       : 0.02
% 35.31/25.00  Main loop            : 23.85
% 35.31/25.00  Inferencing          : 2.25
% 35.31/25.00  Reduction            : 15.55
% 35.31/25.00  Demodulation         : 13.91
% 35.31/25.00  BG Simplification    : 0.29
% 35.31/25.00  Subsumption          : 5.23
% 35.31/25.00  Abstraction          : 0.53
% 35.31/25.00  MUC search           : 0.00
% 35.31/25.00  Cooper               : 0.00
% 35.31/25.00  Total                : 24.23
% 35.31/25.00  Index Insertion      : 0.00
% 35.31/25.00  Index Deletion       : 0.00
% 35.31/25.00  Index Matching       : 0.00
% 35.31/25.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
