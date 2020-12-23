%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:02 EST 2020

% Result     : Theorem 14.68s
% Output     : CNFRefutation 14.68s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 647 expanded)
%              Number of leaves         :   49 ( 245 expanded)
%              Depth                    :   12
%              Number of atoms          :  234 (1353 expanded)
%              Number of equality atoms :   61 ( 407 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_82,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_127,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_90,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_151,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_84,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_313,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_80,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1110,plain,(
    ! [A_155,B_156,C_157] :
      ( k7_subset_1(A_155,B_156,C_157) = k4_xboole_0(B_156,C_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1131,plain,(
    ! [C_157] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_157) = k4_xboole_0('#skF_5',C_157) ),
    inference(resolution,[status(thm)],[c_78,c_1110])).

tff(c_2704,plain,(
    ! [A_246,B_247] :
      ( k7_subset_1(u1_struct_0(A_246),B_247,k2_tops_1(A_246,B_247)) = k1_tops_1(A_246,B_247)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2732,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2704])).

tff(c_2751,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1131,c_2732])).

tff(c_54,plain,(
    ! [A_36,B_37] : k6_subset_1(A_36,B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [A_32,B_33] : m1_subset_1(k6_subset_1(A_32,B_33),k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_91,plain,(
    ! [A_32,B_33] : m1_subset_1(k4_xboole_0(A_32,B_33),k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_168,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_179,plain,(
    ! [A_32,B_33] : r1_tarski(k4_xboole_0(A_32,B_33),A_32) ),
    inference(resolution,[status(thm)],[c_91,c_168])).

tff(c_427,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_442,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,k4_xboole_0(A_32,B_33)) ) ),
    inference(resolution,[status(thm)],[c_179,c_427])).

tff(c_2772,plain,
    ( k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_442])).

tff(c_2797,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_2772])).

tff(c_2852,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2797])).

tff(c_967,plain,(
    ! [A_146,B_147] :
      ( k3_subset_1(A_146,k3_subset_1(A_146,B_147)) = B_147
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_987,plain,(
    ! [A_32,B_33] : k3_subset_1(A_32,k3_subset_1(A_32,k4_xboole_0(A_32,B_33))) = k4_xboole_0(A_32,B_33) ),
    inference(resolution,[status(thm)],[c_91,c_967])).

tff(c_2769,plain,(
    k3_subset_1('#skF_5',k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5'))) = k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_987])).

tff(c_2796,plain,(
    k3_subset_1('#skF_5',k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5'))) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_2769])).

tff(c_630,plain,(
    ! [A_128,B_129] :
      ( k4_xboole_0(A_128,B_129) = k3_subset_1(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2953,plain,(
    ! [A_252,B_253] : k4_xboole_0(A_252,k4_xboole_0(A_252,B_253)) = k3_subset_1(A_252,k4_xboole_0(A_252,B_253)) ),
    inference(resolution,[status(thm)],[c_91,c_630])).

tff(c_2999,plain,(
    k3_subset_1('#skF_5',k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5'))) = k4_xboole_0('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_2953])).

tff(c_3027,plain,(
    k4_xboole_0('#skF_5',k1_tops_1('#skF_4','#skF_5')) = k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_2999])).

tff(c_646,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_subset_1(A_32,k4_xboole_0(A_32,B_33)) ),
    inference(resolution,[status(thm)],[c_91,c_630])).

tff(c_4469,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5'))) = k3_subset_1('#skF_5',k4_xboole_0('#skF_5',k1_tops_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3027,c_646])).

tff(c_4503,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5'))) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2796,c_3027,c_4469])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1208,plain,(
    ! [D_167,A_168,B_169] :
      ( r2_hidden(D_167,k4_xboole_0(A_168,B_169))
      | r2_hidden(D_167,B_169)
      | ~ r2_hidden(D_167,A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13350,plain,(
    ! [A_514,A_515,B_516] :
      ( r1_tarski(A_514,k4_xboole_0(A_515,B_516))
      | r2_hidden('#skF_1'(A_514,k4_xboole_0(A_515,B_516)),B_516)
      | ~ r2_hidden('#skF_1'(A_514,k4_xboole_0(A_515,B_516)),A_515) ) ),
    inference(resolution,[status(thm)],[c_1208,c_4])).

tff(c_21516,plain,(
    ! [A_637,B_638] :
      ( r2_hidden('#skF_1'(A_637,k4_xboole_0(A_637,B_638)),B_638)
      | r1_tarski(A_637,k4_xboole_0(A_637,B_638)) ) ),
    inference(resolution,[status(thm)],[c_6,c_13350])).

tff(c_21678,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5')))
    | r1_tarski('#skF_5',k4_xboole_0('#skF_5',k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4503,c_21516])).

tff(c_21757,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5')))
    | r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4503,c_21678])).

tff(c_21758,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2852,c_21757])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4383,plain,(
    ! [D_297,A_298,B_299] :
      ( r2_hidden(D_297,A_298)
      | ~ r2_hidden(D_297,k3_subset_1(A_298,k4_xboole_0(A_298,B_299))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2953,c_12])).

tff(c_4406,plain,(
    ! [D_297] :
      ( r2_hidden(D_297,'#skF_5')
      | ~ r2_hidden(D_297,k3_subset_1('#skF_5',k1_tops_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_4383])).

tff(c_24214,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_21758,c_4406])).

tff(c_21696,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),k2_tops_1('#skF_4','#skF_5'))
    | r1_tarski('#skF_5',k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_21516])).

tff(c_21764,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),k2_tops_1('#skF_4','#skF_5'))
    | r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_21696])).

tff(c_21765,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),k2_tops_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2852,c_21764])).

tff(c_647,plain,(
    k4_xboole_0(u1_struct_0('#skF_4'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_630])).

tff(c_694,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_91])).

tff(c_2003,plain,(
    ! [A_202,B_203] :
      ( k2_tops_1(A_202,k3_subset_1(u1_struct_0(A_202),B_203)) = k2_tops_1(A_202,B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2027,plain,
    ( k2_tops_1('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2003])).

tff(c_2042,plain,(
    k2_tops_1('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2027])).

tff(c_64,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k2_tops_1(A_45,B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2046,plain,
    ( m1_subset_1(k2_tops_1('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2042,c_64])).

tff(c_2050,plain,(
    m1_subset_1(k2_tops_1('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_694,c_2046])).

tff(c_2853,plain,(
    ! [A_250,B_251] :
      ( k4_subset_1(u1_struct_0(A_250),B_251,k2_tops_1(A_250,B_251)) = k2_pre_topc(A_250,B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2881,plain,
    ( k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2853])).

tff(c_2898,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2881])).

tff(c_48,plain,(
    ! [A_29,B_30,C_31] :
      ( m1_subset_1(k4_subset_1(A_29,B_30,C_31),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2903,plain,
    ( m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_tops_1('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2898,c_48])).

tff(c_2907,plain,(
    m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2050,c_2903])).

tff(c_56,plain,(
    ! [A_38,B_39,C_40] :
      ( k7_subset_1(A_38,B_39,C_40) = k4_xboole_0(B_39,C_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28725,plain,(
    ! [C_706] : k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_706) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_706) ),
    inference(resolution,[status(thm)],[c_2907,c_56])).

tff(c_28742,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28725,c_151])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_29159,plain,(
    ! [D_712] :
      ( ~ r2_hidden(D_712,'#skF_5')
      | ~ r2_hidden(D_712,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28742,c_10])).

tff(c_29182,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k1_tops_1('#skF_4','#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_21765,c_29159])).

tff(c_29284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24214,c_29182])).

tff(c_29285,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2797])).

tff(c_82,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1605,plain,(
    ! [A_182,B_183] :
      ( v3_pre_topc(k1_tops_1(A_182,B_183),A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1621,plain,
    ( v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1605])).

tff(c_1631,plain,(
    v3_pre_topc(k1_tops_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1621])).

tff(c_29291,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29285,c_1631])).

tff(c_29295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_29291])).

tff(c_29296,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_29421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_29296])).

tff(c_29422,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_29546,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29422,c_84])).

tff(c_30413,plain,(
    ! [A_802,B_803,C_804] :
      ( k7_subset_1(A_802,B_803,C_804) = k4_xboole_0(B_803,C_804)
      | ~ m1_subset_1(B_803,k1_zfmisc_1(A_802)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30434,plain,(
    ! [C_804] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_804) = k4_xboole_0('#skF_5',C_804) ),
    inference(resolution,[status(thm)],[c_78,c_30413])).

tff(c_32262,plain,(
    ! [A_898,B_899] :
      ( k7_subset_1(u1_struct_0(A_898),B_899,k2_tops_1(A_898,B_899)) = k1_tops_1(A_898,B_899)
      | ~ m1_subset_1(B_899,k1_zfmisc_1(u1_struct_0(A_898)))
      | ~ l1_pre_topc(A_898) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32295,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_32262])).

tff(c_32318,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_30434,c_32295])).

tff(c_29440,plain,(
    ! [A_731,B_732] :
      ( r1_tarski(A_731,B_732)
      | ~ m1_subset_1(A_731,k1_zfmisc_1(B_732)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_29451,plain,(
    ! [A_32,B_33] : r1_tarski(k4_xboole_0(A_32,B_33),A_32) ),
    inference(resolution,[status(thm)],[c_91,c_29440])).

tff(c_29696,plain,(
    ! [B_758,A_759] :
      ( B_758 = A_759
      | ~ r1_tarski(B_758,A_759)
      | ~ r1_tarski(A_759,B_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29711,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,k4_xboole_0(A_32,B_33)) ) ),
    inference(resolution,[status(thm)],[c_29451,c_29696])).

tff(c_32348,plain,
    ( k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32318,c_29711])).

tff(c_32374,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32318,c_32348])).

tff(c_32461,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32374])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_33968,plain,(
    ! [B_954,A_955,C_956] :
      ( r1_tarski(B_954,k1_tops_1(A_955,C_956))
      | ~ r1_tarski(B_954,C_956)
      | ~ v3_pre_topc(B_954,A_955)
      | ~ m1_subset_1(C_956,k1_zfmisc_1(u1_struct_0(A_955)))
      | ~ m1_subset_1(B_954,k1_zfmisc_1(u1_struct_0(A_955)))
      | ~ l1_pre_topc(A_955) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34007,plain,(
    ! [B_954] :
      ( r1_tarski(B_954,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_954,'#skF_5')
      | ~ v3_pre_topc(B_954,'#skF_4')
      | ~ m1_subset_1(B_954,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_33968])).

tff(c_34034,plain,(
    ! [B_957] :
      ( r1_tarski(B_957,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_957,'#skF_5')
      | ~ v3_pre_topc(B_957,'#skF_4')
      | ~ m1_subset_1(B_957,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_34007])).

tff(c_34090,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_34034])).

tff(c_34113,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29422,c_30,c_34090])).

tff(c_34115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32461,c_34113])).

tff(c_34116,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32374])).

tff(c_68,plain,(
    ! [A_49,B_51] :
      ( k7_subset_1(u1_struct_0(A_49),k2_pre_topc(A_49,B_51),k1_tops_1(A_49,B_51)) = k2_tops_1(A_49,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34133,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34116,c_68])).

tff(c_34137,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_34133])).

tff(c_34139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29546,c_34137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.68/6.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.68/6.74  
% 14.68/6.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.68/6.74  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 14.68/6.74  
% 14.68/6.74  %Foreground sorts:
% 14.68/6.74  
% 14.68/6.74  
% 14.68/6.74  %Background operators:
% 14.68/6.74  
% 14.68/6.74  
% 14.68/6.74  %Foreground operators:
% 14.68/6.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.68/6.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.68/6.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.68/6.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.68/6.74  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.68/6.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.68/6.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.68/6.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.68/6.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.68/6.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.68/6.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.68/6.74  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.68/6.74  tff('#skF_5', type, '#skF_5': $i).
% 14.68/6.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.68/6.74  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.68/6.74  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 14.68/6.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.68/6.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.68/6.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.68/6.74  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.68/6.74  tff('#skF_4', type, '#skF_4': $i).
% 14.68/6.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.68/6.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.68/6.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.68/6.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.68/6.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.68/6.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.68/6.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.68/6.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.68/6.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.68/6.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.68/6.74  
% 14.68/6.77  tff(f_160, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 14.68/6.77  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.68/6.77  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 14.68/6.77  tff(f_82, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.68/6.77  tff(f_76, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 14.68/6.77  tff(f_92, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.68/6.77  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.68/6.77  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.68/6.77  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 14.68/6.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.68/6.77  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.68/6.77  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 14.68/6.77  tff(f_98, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 14.68/6.77  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 14.68/6.77  tff(f_74, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 14.68/6.77  tff(f_106, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 14.68/6.77  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 14.68/6.77  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 14.68/6.77  tff(c_90, plain, (v3_pre_topc('#skF_5', '#skF_4') | k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.68/6.77  tff(c_151, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_90])).
% 14.68/6.77  tff(c_84, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.68/6.77  tff(c_313, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 14.68/6.77  tff(c_80, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.68/6.77  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.68/6.77  tff(c_1110, plain, (![A_155, B_156, C_157]: (k7_subset_1(A_155, B_156, C_157)=k4_xboole_0(B_156, C_157) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.68/6.77  tff(c_1131, plain, (![C_157]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_157)=k4_xboole_0('#skF_5', C_157))), inference(resolution, [status(thm)], [c_78, c_1110])).
% 14.68/6.77  tff(c_2704, plain, (![A_246, B_247]: (k7_subset_1(u1_struct_0(A_246), B_247, k2_tops_1(A_246, B_247))=k1_tops_1(A_246, B_247) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.68/6.77  tff(c_2732, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2704])).
% 14.68/6.77  tff(c_2751, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1131, c_2732])).
% 14.68/6.77  tff(c_54, plain, (![A_36, B_37]: (k6_subset_1(A_36, B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.68/6.77  tff(c_50, plain, (![A_32, B_33]: (m1_subset_1(k6_subset_1(A_32, B_33), k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.68/6.77  tff(c_91, plain, (![A_32, B_33]: (m1_subset_1(k4_xboole_0(A_32, B_33), k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 14.68/6.77  tff(c_168, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.68/6.77  tff(c_179, plain, (![A_32, B_33]: (r1_tarski(k4_xboole_0(A_32, B_33), A_32))), inference(resolution, [status(thm)], [c_91, c_168])).
% 14.68/6.77  tff(c_427, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.68/6.77  tff(c_442, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, k4_xboole_0(A_32, B_33)))), inference(resolution, [status(thm)], [c_179, c_427])).
% 14.68/6.77  tff(c_2772, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_442])).
% 14.68/6.77  tff(c_2797, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_2772])).
% 14.68/6.77  tff(c_2852, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2797])).
% 14.68/6.77  tff(c_967, plain, (![A_146, B_147]: (k3_subset_1(A_146, k3_subset_1(A_146, B_147))=B_147 | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.68/6.77  tff(c_987, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, k4_xboole_0(A_32, B_33)))=k4_xboole_0(A_32, B_33))), inference(resolution, [status(thm)], [c_91, c_967])).
% 14.68/6.77  tff(c_2769, plain, (k3_subset_1('#skF_5', k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5')))=k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_987])).
% 14.68/6.77  tff(c_2796, plain, (k3_subset_1('#skF_5', k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5')))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_2769])).
% 14.68/6.77  tff(c_630, plain, (![A_128, B_129]: (k4_xboole_0(A_128, B_129)=k3_subset_1(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.68/6.77  tff(c_2953, plain, (![A_252, B_253]: (k4_xboole_0(A_252, k4_xboole_0(A_252, B_253))=k3_subset_1(A_252, k4_xboole_0(A_252, B_253)))), inference(resolution, [status(thm)], [c_91, c_630])).
% 14.68/6.77  tff(c_2999, plain, (k3_subset_1('#skF_5', k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5')))=k4_xboole_0('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_2953])).
% 14.68/6.77  tff(c_3027, plain, (k4_xboole_0('#skF_5', k1_tops_1('#skF_4', '#skF_5'))=k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_2999])).
% 14.68/6.77  tff(c_646, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_subset_1(A_32, k4_xboole_0(A_32, B_33)))), inference(resolution, [status(thm)], [c_91, c_630])).
% 14.68/6.77  tff(c_4469, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5')))=k3_subset_1('#skF_5', k4_xboole_0('#skF_5', k1_tops_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3027, c_646])).
% 14.68/6.77  tff(c_4503, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5')))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2796, c_3027, c_4469])).
% 14.68/6.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.68/6.77  tff(c_1208, plain, (![D_167, A_168, B_169]: (r2_hidden(D_167, k4_xboole_0(A_168, B_169)) | r2_hidden(D_167, B_169) | ~r2_hidden(D_167, A_168))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.68/6.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.68/6.77  tff(c_13350, plain, (![A_514, A_515, B_516]: (r1_tarski(A_514, k4_xboole_0(A_515, B_516)) | r2_hidden('#skF_1'(A_514, k4_xboole_0(A_515, B_516)), B_516) | ~r2_hidden('#skF_1'(A_514, k4_xboole_0(A_515, B_516)), A_515))), inference(resolution, [status(thm)], [c_1208, c_4])).
% 14.68/6.77  tff(c_21516, plain, (![A_637, B_638]: (r2_hidden('#skF_1'(A_637, k4_xboole_0(A_637, B_638)), B_638) | r1_tarski(A_637, k4_xboole_0(A_637, B_638)))), inference(resolution, [status(thm)], [c_6, c_13350])).
% 14.68/6.77  tff(c_21678, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5'))) | r1_tarski('#skF_5', k4_xboole_0('#skF_5', k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_4503, c_21516])).
% 14.68/6.77  tff(c_21757, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5'))) | r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4503, c_21678])).
% 14.68/6.77  tff(c_21758, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2852, c_21757])).
% 14.68/6.77  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.68/6.77  tff(c_4383, plain, (![D_297, A_298, B_299]: (r2_hidden(D_297, A_298) | ~r2_hidden(D_297, k3_subset_1(A_298, k4_xboole_0(A_298, B_299))))), inference(superposition, [status(thm), theory('equality')], [c_2953, c_12])).
% 14.68/6.77  tff(c_4406, plain, (![D_297]: (r2_hidden(D_297, '#skF_5') | ~r2_hidden(D_297, k3_subset_1('#skF_5', k1_tops_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_4383])).
% 14.68/6.77  tff(c_24214, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_21758, c_4406])).
% 14.68/6.77  tff(c_21696, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), k2_tops_1('#skF_4', '#skF_5')) | r1_tarski('#skF_5', k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_21516])).
% 14.68/6.77  tff(c_21764, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), k2_tops_1('#skF_4', '#skF_5')) | r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_21696])).
% 14.68/6.77  tff(c_21765, plain, (r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), k2_tops_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2852, c_21764])).
% 14.68/6.77  tff(c_647, plain, (k4_xboole_0(u1_struct_0('#skF_4'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_78, c_630])).
% 14.68/6.77  tff(c_694, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_647, c_91])).
% 14.68/6.77  tff(c_2003, plain, (![A_202, B_203]: (k2_tops_1(A_202, k3_subset_1(u1_struct_0(A_202), B_203))=k2_tops_1(A_202, B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.68/6.77  tff(c_2027, plain, (k2_tops_1('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))=k2_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2003])).
% 14.68/6.77  tff(c_2042, plain, (k2_tops_1('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2027])).
% 14.68/6.77  tff(c_64, plain, (![A_45, B_46]: (m1_subset_1(k2_tops_1(A_45, B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.68/6.77  tff(c_2046, plain, (m1_subset_1(k2_tops_1('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2042, c_64])).
% 14.68/6.77  tff(c_2050, plain, (m1_subset_1(k2_tops_1('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_694, c_2046])).
% 14.68/6.77  tff(c_2853, plain, (![A_250, B_251]: (k4_subset_1(u1_struct_0(A_250), B_251, k2_tops_1(A_250, B_251))=k2_pre_topc(A_250, B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_141])).
% 14.68/6.77  tff(c_2881, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2853])).
% 14.68/6.77  tff(c_2898, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2881])).
% 14.68/6.77  tff(c_48, plain, (![A_29, B_30, C_31]: (m1_subset_1(k4_subset_1(A_29, B_30, C_31), k1_zfmisc_1(A_29)) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.68/6.77  tff(c_2903, plain, (m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_tops_1('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2898, c_48])).
% 14.68/6.77  tff(c_2907, plain, (m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2050, c_2903])).
% 14.68/6.77  tff(c_56, plain, (![A_38, B_39, C_40]: (k7_subset_1(A_38, B_39, C_40)=k4_xboole_0(B_39, C_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.68/6.77  tff(c_28725, plain, (![C_706]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_706)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_706))), inference(resolution, [status(thm)], [c_2907, c_56])).
% 14.68/6.77  tff(c_28742, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28725, c_151])).
% 14.68/6.77  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.68/6.77  tff(c_29159, plain, (![D_712]: (~r2_hidden(D_712, '#skF_5') | ~r2_hidden(D_712, k2_tops_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_28742, c_10])).
% 14.68/6.77  tff(c_29182, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tops_1('#skF_4', '#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_21765, c_29159])).
% 14.68/6.77  tff(c_29284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24214, c_29182])).
% 14.68/6.77  tff(c_29285, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_2797])).
% 14.68/6.77  tff(c_82, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 14.68/6.77  tff(c_1605, plain, (![A_182, B_183]: (v3_pre_topc(k1_tops_1(A_182, B_183), A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.68/6.77  tff(c_1621, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1605])).
% 14.68/6.77  tff(c_1631, plain, (v3_pre_topc(k1_tops_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1621])).
% 14.68/6.77  tff(c_29291, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29285, c_1631])).
% 14.68/6.77  tff(c_29295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_29291])).
% 14.68/6.77  tff(c_29296, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_84])).
% 14.68/6.77  tff(c_29421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_29296])).
% 14.68/6.77  tff(c_29422, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 14.68/6.77  tff(c_29546, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_29422, c_84])).
% 14.68/6.77  tff(c_30413, plain, (![A_802, B_803, C_804]: (k7_subset_1(A_802, B_803, C_804)=k4_xboole_0(B_803, C_804) | ~m1_subset_1(B_803, k1_zfmisc_1(A_802)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.68/6.77  tff(c_30434, plain, (![C_804]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_804)=k4_xboole_0('#skF_5', C_804))), inference(resolution, [status(thm)], [c_78, c_30413])).
% 14.68/6.77  tff(c_32262, plain, (![A_898, B_899]: (k7_subset_1(u1_struct_0(A_898), B_899, k2_tops_1(A_898, B_899))=k1_tops_1(A_898, B_899) | ~m1_subset_1(B_899, k1_zfmisc_1(u1_struct_0(A_898))) | ~l1_pre_topc(A_898))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.68/6.77  tff(c_32295, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_32262])).
% 14.68/6.77  tff(c_32318, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_30434, c_32295])).
% 14.68/6.77  tff(c_29440, plain, (![A_731, B_732]: (r1_tarski(A_731, B_732) | ~m1_subset_1(A_731, k1_zfmisc_1(B_732)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.68/6.77  tff(c_29451, plain, (![A_32, B_33]: (r1_tarski(k4_xboole_0(A_32, B_33), A_32))), inference(resolution, [status(thm)], [c_91, c_29440])).
% 14.68/6.77  tff(c_29696, plain, (![B_758, A_759]: (B_758=A_759 | ~r1_tarski(B_758, A_759) | ~r1_tarski(A_759, B_758))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.68/6.77  tff(c_29711, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, k4_xboole_0(A_32, B_33)))), inference(resolution, [status(thm)], [c_29451, c_29696])).
% 14.68/6.77  tff(c_32348, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32318, c_29711])).
% 14.68/6.77  tff(c_32374, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32318, c_32348])).
% 14.68/6.77  tff(c_32461, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_32374])).
% 14.68/6.77  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.68/6.77  tff(c_33968, plain, (![B_954, A_955, C_956]: (r1_tarski(B_954, k1_tops_1(A_955, C_956)) | ~r1_tarski(B_954, C_956) | ~v3_pre_topc(B_954, A_955) | ~m1_subset_1(C_956, k1_zfmisc_1(u1_struct_0(A_955))) | ~m1_subset_1(B_954, k1_zfmisc_1(u1_struct_0(A_955))) | ~l1_pre_topc(A_955))), inference(cnfTransformation, [status(thm)], [f_127])).
% 14.68/6.77  tff(c_34007, plain, (![B_954]: (r1_tarski(B_954, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_954, '#skF_5') | ~v3_pre_topc(B_954, '#skF_4') | ~m1_subset_1(B_954, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_33968])).
% 14.68/6.77  tff(c_34034, plain, (![B_957]: (r1_tarski(B_957, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_957, '#skF_5') | ~v3_pre_topc(B_957, '#skF_4') | ~m1_subset_1(B_957, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_34007])).
% 14.68/6.77  tff(c_34090, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_34034])).
% 14.68/6.77  tff(c_34113, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_29422, c_30, c_34090])).
% 14.68/6.77  tff(c_34115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32461, c_34113])).
% 14.68/6.77  tff(c_34116, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_32374])).
% 14.68/6.77  tff(c_68, plain, (![A_49, B_51]: (k7_subset_1(u1_struct_0(A_49), k2_pre_topc(A_49, B_51), k1_tops_1(A_49, B_51))=k2_tops_1(A_49, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.68/6.77  tff(c_34133, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34116, c_68])).
% 14.68/6.77  tff(c_34137, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_34133])).
% 14.68/6.77  tff(c_34139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29546, c_34137])).
% 14.68/6.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.68/6.77  
% 14.68/6.77  Inference rules
% 14.68/6.77  ----------------------
% 14.68/6.77  #Ref     : 0
% 14.68/6.77  #Sup     : 8156
% 14.68/6.77  #Fact    : 0
% 14.68/6.77  #Define  : 0
% 14.68/6.77  #Split   : 16
% 14.68/6.77  #Chain   : 0
% 14.68/6.77  #Close   : 0
% 14.68/6.77  
% 14.68/6.77  Ordering : KBO
% 14.68/6.77  
% 14.68/6.77  Simplification rules
% 14.68/6.77  ----------------------
% 14.68/6.77  #Subsume      : 762
% 14.68/6.77  #Demod        : 8570
% 14.68/6.77  #Tautology    : 3665
% 14.68/6.77  #SimpNegUnit  : 21
% 14.68/6.77  #BackRed      : 50
% 14.68/6.77  
% 14.68/6.77  #Partial instantiations: 0
% 14.68/6.77  #Strategies tried      : 1
% 14.68/6.77  
% 14.68/6.77  Timing (in seconds)
% 14.68/6.77  ----------------------
% 14.68/6.77  Preprocessing        : 0.37
% 14.68/6.77  Parsing              : 0.19
% 14.68/6.77  CNF conversion       : 0.03
% 14.68/6.77  Main loop            : 5.62
% 14.68/6.77  Inferencing          : 1.10
% 14.68/6.77  Reduction            : 2.86
% 14.68/6.77  Demodulation         : 2.44
% 14.68/6.77  BG Simplification    : 0.12
% 14.68/6.77  Subsumption          : 1.22
% 14.68/6.77  Abstraction          : 0.20
% 14.68/6.77  MUC search           : 0.00
% 14.68/6.77  Cooper               : 0.00
% 14.68/6.77  Total                : 6.03
% 14.68/6.77  Index Insertion      : 0.00
% 14.68/6.77  Index Deletion       : 0.00
% 14.68/6.77  Index Matching       : 0.00
% 14.68/6.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
