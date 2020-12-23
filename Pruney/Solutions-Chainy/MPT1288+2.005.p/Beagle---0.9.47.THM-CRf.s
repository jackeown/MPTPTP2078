%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:26 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 556 expanded)
%              Number of leaves         :   37 ( 204 expanded)
%              Depth                    :   21
%              Number of atoms          :  256 (1570 expanded)
%              Number of equality atoms :   32 ( 216 expanded)
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

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => k1_tops_1(A,k2_tops_1(A,B)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_161,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => ( v3_tops_1(B,A)
            <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_44,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_129,plain,(
    ! [A_67,B_68] :
      ( k1_tops_1(A_67,k1_tops_1(A_67,B_68)) = k1_tops_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_137,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_129])).

tff(c_143,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_137])).

tff(c_116,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k1_tops_1(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( v4_pre_topc(k2_pre_topc(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_200,plain,(
    ! [A_85,B_86] :
      ( v4_pre_topc(k2_pre_topc(A_85,k1_tops_1(A_85,B_86)),A_85)
      | ~ v2_pre_topc(A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_116,c_24])).

tff(c_203,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_200])).

tff(c_205,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_203])).

tff(c_206,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_209,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_206])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_209])).

tff(c_215,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_62,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_62])).

tff(c_67,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_10,plain,(
    ! [A_5,B_9,C_11] :
      ( r1_tarski(k2_pre_topc(A_5,B_9),k2_pre_topc(A_5,C_11))
      | ~ r1_tarski(B_9,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( r1_tarski(B_14,k2_pre_topc(A_12,k1_tops_1(A_12,B_14)))
      | ~ v4_tops_1(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_214,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1026,plain,(
    ! [A_116,B_117] :
      ( k1_tops_1(A_116,k1_tops_1(A_116,k2_pre_topc(A_116,B_117))) = k1_tops_1(A_116,k2_pre_topc(A_116,B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_8,c_129])).

tff(c_1034,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_1026])).

tff(c_1054,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1034])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( v3_pre_topc(k1_tops_1(A_23,B_24),A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_125,plain,(
    ! [A_65,B_66] :
      ( v3_pre_topc(k1_tops_1(A_65,k1_tops_1(A_65,B_66)),A_65)
      | ~ v2_pre_topc(A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_116,c_26])).

tff(c_2082,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_125])).

tff(c_2112,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_2082])).

tff(c_7244,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2112])).

tff(c_7256,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_7244])).

tff(c_7260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_215,c_7256])).

tff(c_7262,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2112])).

tff(c_867,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(k2_pre_topc(A_110,C_111),B_112)
      | ~ r1_tarski(C_111,B_112)
      | ~ v4_pre_topc(B_112,A_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_883,plain,(
    ! [B_112] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_112)
      | ~ r1_tarski('#skF_2',B_112)
      | ~ v4_pre_topc(B_112,'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_867])).

tff(c_901,plain,(
    ! [B_112] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_112)
      | ~ r1_tarski('#skF_2',B_112)
      | ~ v4_pre_topc(B_112,'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_883])).

tff(c_7274,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7262,c_901])).

tff(c_7311,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_7274])).

tff(c_7342,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7311])).

tff(c_7345,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_7342])).

tff(c_7349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_7345])).

tff(c_7350,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_7311])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7377,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7350,c_2])).

tff(c_7515,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7377])).

tff(c_7518,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_7515])).

tff(c_7522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_215,c_48,c_67,c_7518])).

tff(c_7523,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_7377])).

tff(c_562,plain,(
    ! [A_105,B_106] :
      ( k7_subset_1(u1_struct_0(A_105),k2_pre_topc(A_105,B_106),k1_tops_1(A_105,B_106)) = k2_tops_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_577,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_562])).

tff(c_585,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_215,c_577])).

tff(c_7537,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7523,c_585])).

tff(c_28,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7661,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7537,c_28])).

tff(c_7668,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_7661])).

tff(c_94,plain,(
    ! [A_61,B_62] :
      ( v3_pre_topc(k1_tops_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_98,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_102,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_98])).

tff(c_42,plain,(
    ! [A_46,B_48] :
      ( v3_tops_1(k2_tops_1(A_46,B_48),A_46)
      | ~ v3_pre_topc(B_48,A_46)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_239,plain,
    ( v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_42])).

tff(c_255,plain,(
    v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_102,c_239])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( v4_pre_topc(k2_tops_1(A_19,B_20),A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_245,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_22])).

tff(c_264,plain,(
    v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_245])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_216,plain,(
    ! [A_87,B_88] :
      ( k2_tops_1(A_87,B_88) = B_88
      | ~ v3_tops_1(B_88,A_87)
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6093,plain,(
    ! [A_180,B_181] :
      ( k2_tops_1(A_180,k2_tops_1(A_180,B_181)) = k2_tops_1(A_180,B_181)
      | ~ v3_tops_1(k2_tops_1(A_180,B_181),A_180)
      | ~ v4_pre_topc(k2_tops_1(A_180,B_181),A_180)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_20,c_216])).

tff(c_6115,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_264,c_6093])).

tff(c_6147,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_215,c_255,c_6115])).

tff(c_320,plain,(
    ! [A_101,B_102] :
      ( k1_tops_1(A_101,k2_tops_1(A_101,k2_tops_1(A_101,B_102))) = k1_xboole_0
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_322,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_320])).

tff(c_333,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_322])).

tff(c_6153,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6147,c_333])).

tff(c_7679,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7668,c_6153])).

tff(c_7685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_7679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.07  
% 8.41/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.07  %$ v4_tops_1 > v4_pre_topc > v3_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.41/3.07  
% 8.41/3.07  %Foreground sorts:
% 8.41/3.07  
% 8.41/3.07  
% 8.41/3.07  %Background operators:
% 8.41/3.07  
% 8.41/3.07  
% 8.41/3.07  %Foreground operators:
% 8.41/3.07  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.41/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/3.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.41/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.41/3.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.41/3.07  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 8.41/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.41/3.07  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 8.41/3.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.41/3.07  tff('#skF_2', type, '#skF_2': $i).
% 8.41/3.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.41/3.07  tff('#skF_1', type, '#skF_1': $i).
% 8.41/3.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.41/3.07  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.41/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/3.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.41/3.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.41/3.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.41/3.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.41/3.07  
% 8.41/3.09  tff(f_173, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (k1_tops_1(A, k2_tops_1(A, B)) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_tops_1)).
% 8.41/3.09  tff(f_66, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 8.41/3.09  tff(f_118, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 8.41/3.09  tff(f_88, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 8.41/3.09  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 8.41/3.09  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 8.41/3.09  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 8.41/3.09  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.41/3.09  tff(f_96, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 8.41/3.09  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 8.41/3.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.41/3.09  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.41/3.09  tff(f_161, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tops_1)).
% 8.41/3.09  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_tops_1)).
% 8.41/3.09  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.41/3.09  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 8.41/3.09  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 8.41/3.09  tff(c_44, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.41/3.09  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.41/3.09  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.41/3.09  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.41/3.09  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.41/3.09  tff(c_129, plain, (![A_67, B_68]: (k1_tops_1(A_67, k1_tops_1(A_67, B_68))=k1_tops_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.41/3.09  tff(c_137, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_129])).
% 8.41/3.09  tff(c_143, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_137])).
% 8.41/3.09  tff(c_116, plain, (![A_65, B_66]: (m1_subset_1(k1_tops_1(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.41/3.09  tff(c_24, plain, (![A_21, B_22]: (v4_pre_topc(k2_pre_topc(A_21, B_22), A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.41/3.09  tff(c_200, plain, (![A_85, B_86]: (v4_pre_topc(k2_pre_topc(A_85, k1_tops_1(A_85, B_86)), A_85) | ~v2_pre_topc(A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_116, c_24])).
% 8.41/3.09  tff(c_203, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_143, c_200])).
% 8.41/3.09  tff(c_205, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_203])).
% 8.41/3.09  tff(c_206, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_205])).
% 8.41/3.09  tff(c_209, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_206])).
% 8.41/3.09  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_209])).
% 8.41/3.09  tff(c_215, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_205])).
% 8.41/3.09  tff(c_62, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.41/3.09  tff(c_64, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_62])).
% 8.41/3.09  tff(c_67, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64])).
% 8.41/3.09  tff(c_10, plain, (![A_5, B_9, C_11]: (r1_tarski(k2_pre_topc(A_5, B_9), k2_pre_topc(A_5, C_11)) | ~r1_tarski(B_9, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.41/3.09  tff(c_46, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.41/3.09  tff(c_14, plain, (![B_14, A_12]: (r1_tarski(B_14, k2_pre_topc(A_12, k1_tops_1(A_12, B_14))) | ~v4_tops_1(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.41/3.09  tff(c_214, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_205])).
% 8.41/3.09  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.41/3.09  tff(c_1026, plain, (![A_116, B_117]: (k1_tops_1(A_116, k1_tops_1(A_116, k2_pre_topc(A_116, B_117)))=k1_tops_1(A_116, k2_pre_topc(A_116, B_117)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_8, c_129])).
% 8.41/3.09  tff(c_1034, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_1026])).
% 8.41/3.09  tff(c_1054, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1034])).
% 8.41/3.09  tff(c_26, plain, (![A_23, B_24]: (v3_pre_topc(k1_tops_1(A_23, B_24), A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.41/3.09  tff(c_125, plain, (![A_65, B_66]: (v3_pre_topc(k1_tops_1(A_65, k1_tops_1(A_65, B_66)), A_65) | ~v2_pre_topc(A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_116, c_26])).
% 8.41/3.09  tff(c_2082, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1054, c_125])).
% 8.41/3.09  tff(c_2112, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_2082])).
% 8.41/3.09  tff(c_7244, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2112])).
% 8.41/3.09  tff(c_7256, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_7244])).
% 8.41/3.09  tff(c_7260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_215, c_7256])).
% 8.41/3.09  tff(c_7262, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2112])).
% 8.41/3.09  tff(c_867, plain, (![A_110, C_111, B_112]: (r1_tarski(k2_pre_topc(A_110, C_111), B_112) | ~r1_tarski(C_111, B_112) | ~v4_pre_topc(B_112, A_110) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.41/3.09  tff(c_883, plain, (![B_112]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_112) | ~r1_tarski('#skF_2', B_112) | ~v4_pre_topc(B_112, '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_867])).
% 8.41/3.09  tff(c_901, plain, (![B_112]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_112) | ~r1_tarski('#skF_2', B_112) | ~v4_pre_topc(B_112, '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_883])).
% 8.41/3.09  tff(c_7274, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_7262, c_901])).
% 8.41/3.09  tff(c_7311, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_7274])).
% 8.41/3.09  tff(c_7342, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7311])).
% 8.41/3.09  tff(c_7345, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_7342])).
% 8.41/3.09  tff(c_7349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_7345])).
% 8.41/3.09  tff(c_7350, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_7311])).
% 8.41/3.09  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.09  tff(c_7377, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_7350, c_2])).
% 8.41/3.09  tff(c_7515, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7377])).
% 8.41/3.09  tff(c_7518, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_7515])).
% 8.41/3.09  tff(c_7522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_215, c_48, c_67, c_7518])).
% 8.41/3.09  tff(c_7523, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_7377])).
% 8.41/3.09  tff(c_562, plain, (![A_105, B_106]: (k7_subset_1(u1_struct_0(A_105), k2_pre_topc(A_105, B_106), k1_tops_1(A_105, B_106))=k2_tops_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.41/3.09  tff(c_577, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_143, c_562])).
% 8.41/3.09  tff(c_585, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_215, c_577])).
% 8.41/3.09  tff(c_7537, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7523, c_585])).
% 8.41/3.09  tff(c_28, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.41/3.09  tff(c_7661, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7537, c_28])).
% 8.41/3.09  tff(c_7668, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_7661])).
% 8.41/3.09  tff(c_94, plain, (![A_61, B_62]: (v3_pre_topc(k1_tops_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.41/3.09  tff(c_98, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_94])).
% 8.41/3.09  tff(c_102, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_98])).
% 8.41/3.09  tff(c_42, plain, (![A_46, B_48]: (v3_tops_1(k2_tops_1(A_46, B_48), A_46) | ~v3_pre_topc(B_48, A_46) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.41/3.09  tff(c_239, plain, (v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_42])).
% 8.41/3.09  tff(c_255, plain, (v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_102, c_239])).
% 8.41/3.09  tff(c_22, plain, (![A_19, B_20]: (v4_pre_topc(k2_tops_1(A_19, B_20), A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.41/3.09  tff(c_245, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_22])).
% 8.41/3.09  tff(c_264, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_245])).
% 8.41/3.09  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k2_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.41/3.09  tff(c_216, plain, (![A_87, B_88]: (k2_tops_1(A_87, B_88)=B_88 | ~v3_tops_1(B_88, A_87) | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.41/3.09  tff(c_6093, plain, (![A_180, B_181]: (k2_tops_1(A_180, k2_tops_1(A_180, B_181))=k2_tops_1(A_180, B_181) | ~v3_tops_1(k2_tops_1(A_180, B_181), A_180) | ~v4_pre_topc(k2_tops_1(A_180, B_181), A_180) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(resolution, [status(thm)], [c_20, c_216])).
% 8.41/3.09  tff(c_6115, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_264, c_6093])).
% 8.41/3.09  tff(c_6147, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_215, c_255, c_6115])).
% 8.41/3.09  tff(c_320, plain, (![A_101, B_102]: (k1_tops_1(A_101, k2_tops_1(A_101, k2_tops_1(A_101, B_102)))=k1_xboole_0 | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.41/3.09  tff(c_322, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_320])).
% 8.41/3.09  tff(c_333, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_322])).
% 8.41/3.09  tff(c_6153, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6147, c_333])).
% 8.41/3.09  tff(c_7679, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7668, c_6153])).
% 8.41/3.09  tff(c_7685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_7679])).
% 8.41/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.09  
% 8.41/3.09  Inference rules
% 8.41/3.09  ----------------------
% 8.41/3.09  #Ref     : 0
% 8.41/3.09  #Sup     : 1601
% 8.41/3.09  #Fact    : 0
% 8.41/3.09  #Define  : 0
% 8.41/3.09  #Split   : 76
% 8.41/3.09  #Chain   : 0
% 8.41/3.09  #Close   : 0
% 8.41/3.09  
% 8.41/3.09  Ordering : KBO
% 8.41/3.09  
% 8.41/3.09  Simplification rules
% 8.41/3.09  ----------------------
% 8.41/3.09  #Subsume      : 198
% 8.41/3.09  #Demod        : 3555
% 8.41/3.09  #Tautology    : 646
% 8.41/3.09  #SimpNegUnit  : 30
% 8.41/3.09  #BackRed      : 56
% 8.41/3.09  
% 8.41/3.09  #Partial instantiations: 0
% 8.41/3.09  #Strategies tried      : 1
% 8.41/3.09  
% 8.41/3.09  Timing (in seconds)
% 8.41/3.09  ----------------------
% 8.41/3.10  Preprocessing        : 0.33
% 8.41/3.10  Parsing              : 0.18
% 8.41/3.10  CNF conversion       : 0.02
% 8.41/3.10  Main loop            : 1.99
% 8.41/3.10  Inferencing          : 0.48
% 8.41/3.10  Reduction            : 0.95
% 8.41/3.10  Demodulation         : 0.74
% 8.41/3.10  BG Simplification    : 0.05
% 8.41/3.10  Subsumption          : 0.40
% 8.41/3.10  Abstraction          : 0.07
% 8.41/3.10  MUC search           : 0.00
% 8.41/3.10  Cooper               : 0.00
% 8.41/3.10  Total                : 2.36
% 8.41/3.10  Index Insertion      : 0.00
% 8.41/3.10  Index Deletion       : 0.00
% 8.41/3.10  Index Matching       : 0.00
% 8.41/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
