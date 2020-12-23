%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 43.78s
% Output     : CNFRefutation 43.88s
% Verified   : 
% Statistics : Number of formulae       :  149 (1707 expanded)
%              Number of leaves         :   47 ( 581 expanded)
%              Depth                    :   16
%              Number of atoms          :  238 (3933 expanded)
%              Number of equality atoms :   68 ( 901 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_66,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_60,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_82,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1123,plain,(
    ! [A_166,B_167] :
      ( k4_subset_1(u1_struct_0(A_166),B_167,k2_tops_1(A_166,B_167)) = k2_pre_topc(A_166,B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1138,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1123])).

tff(c_1151,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1138])).

tff(c_42,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_tops_1(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_854,plain,(
    ! [A_148,B_149,C_150] :
      ( m1_subset_1(k4_subset_1(A_148,B_149,C_150),k1_zfmisc_1(A_148))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1973,plain,(
    ! [A_187,B_188,C_189] :
      ( r1_tarski(k4_subset_1(A_187,B_188,C_189),A_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(A_187))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_854,c_38])).

tff(c_2002,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_1973])).

tff(c_2021,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2002])).

tff(c_2165,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2021])).

tff(c_2168,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2165])).

tff(c_2175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2168])).

tff(c_2177,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2021])).

tff(c_2348,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2177,c_38])).

tff(c_40,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1014,plain,(
    ! [A_158,B_159,C_160] :
      ( k4_subset_1(A_158,B_159,C_160) = k2_xboole_0(B_159,C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(A_158))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2615,plain,(
    ! [B_198,B_199,A_200] :
      ( k4_subset_1(B_198,B_199,A_200) = k2_xboole_0(B_199,A_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(B_198))
      | ~ r1_tarski(A_200,B_198) ) ),
    inference(resolution,[status(thm)],[c_40,c_1014])).

tff(c_2703,plain,(
    ! [A_201] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_201) = k2_xboole_0('#skF_3',A_201)
      | ~ r1_tarski(A_201,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_2615])).

tff(c_2712,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2348,c_2703])).

tff(c_2803,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_2712])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2853,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_12])).

tff(c_2176,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2021])).

tff(c_322,plain,(
    ! [A_106,B_107,C_108] :
      ( k7_subset_1(A_106,B_107,C_108) = k4_xboole_0(B_107,C_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_332,plain,(
    ! [B_38,A_37,C_108] :
      ( k7_subset_1(B_38,A_37,C_108) = k4_xboole_0(A_37,C_108)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_40,c_322])).

tff(c_2588,plain,(
    ! [C_197] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_197) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_197) ),
    inference(resolution,[status(thm)],[c_2176,c_332])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_136,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_66])).

tff(c_2598,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_136])).

tff(c_163,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k3_subset_1(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [B_92,A_93] :
      ( k4_xboole_0(B_92,A_93) = k3_subset_1(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(resolution,[status(thm)],[c_40,c_163])).

tff(c_251,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),A_7) = k3_subset_1(k2_xboole_0(A_7,B_8),A_7) ),
    inference(resolution,[status(thm)],[c_12,c_222])).

tff(c_2844,plain,(
    k3_subset_1(k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')),'#skF_3') = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_251])).

tff(c_2859,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_2598,c_2844])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2885,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2859,c_18])).

tff(c_87564,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2885])).

tff(c_87567,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_87564])).

tff(c_87571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2853,c_87567])).

tff(c_87573,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2885])).

tff(c_309,plain,(
    ! [A_104,B_105] :
      ( k3_subset_1(A_104,k3_subset_1(A_104,B_105)) = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_319,plain,(
    ! [B_38,A_37] :
      ( k3_subset_1(B_38,k3_subset_1(B_38,A_37)) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_40,c_309])).

tff(c_2879,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2859,c_319])).

tff(c_2890,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2853,c_2879])).

tff(c_333,plain,(
    ! [C_108] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_108) = k4_xboole_0('#skF_3',C_108) ),
    inference(resolution,[status(thm)],[c_54,c_322])).

tff(c_1335,plain,(
    ! [A_169,B_170] :
      ( k7_subset_1(u1_struct_0(A_169),B_170,k2_tops_1(A_169,B_170)) = k1_tops_1(A_169,B_170)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1352,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1335])).

tff(c_1368,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_333,c_1352])).

tff(c_442,plain,(
    ! [B_115,A_116,C_117] :
      ( k7_subset_1(B_115,A_116,C_117) = k4_xboole_0(A_116,C_117)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(resolution,[status(thm)],[c_40,c_322])).

tff(c_470,plain,(
    ! [A_7,B_8,C_117] : k7_subset_1(k2_xboole_0(A_7,B_8),A_7,C_117) = k4_xboole_0(A_7,C_117) ),
    inference(resolution,[status(thm)],[c_12,c_442])).

tff(c_2847,plain,(
    ! [C_117] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_117) = k4_xboole_0('#skF_3',C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_470])).

tff(c_28,plain,(
    ! [A_23] : m1_subset_1('#skF_1'(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_142,plain,(
    ! [A_81,B_82,C_83] :
      ( k9_subset_1(A_81,B_82,B_82) = B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,(
    ! [A_23,B_82] : k9_subset_1(A_23,B_82,B_82) = B_82 ),
    inference(resolution,[status(thm)],[c_28,c_142])).

tff(c_1483,plain,(
    ! [A_171,B_172,C_173] :
      ( k9_subset_1(A_171,B_172,k3_subset_1(A_171,C_173)) = k7_subset_1(A_171,B_172,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8900,plain,(
    ! [A_336,B_337,B_338] :
      ( k9_subset_1(A_336,B_337,k3_subset_1(A_336,k3_subset_1(A_336,B_338))) = k7_subset_1(A_336,B_337,k3_subset_1(A_336,B_338))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(A_336))
      | ~ m1_subset_1(B_338,k1_zfmisc_1(A_336)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1483])).

tff(c_109921,plain,(
    ! [A_982,B_983] :
      ( k7_subset_1(A_982,k3_subset_1(A_982,k3_subset_1(A_982,B_983)),k3_subset_1(A_982,B_983)) = k3_subset_1(A_982,k3_subset_1(A_982,B_983))
      | ~ m1_subset_1(k3_subset_1(A_982,k3_subset_1(A_982,B_983)),k1_zfmisc_1(A_982))
      | ~ m1_subset_1(B_983,k1_zfmisc_1(A_982)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8900])).

tff(c_109977,plain,
    ( k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2859,c_109921])).

tff(c_110027,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87573,c_87573,c_2890,c_1368,c_2859,c_2890,c_2859,c_2847,c_2890,c_2859,c_109977])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_1389,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_129])).

tff(c_1400,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1368,c_1389])).

tff(c_1431,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1400])).

tff(c_110083,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110027,c_1431])).

tff(c_110127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_110083])).

tff(c_110128,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1400])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_490,plain,(
    ! [A_123,B_124] :
      ( v3_pre_topc(k1_tops_1(A_123,B_124),A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_498,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_490])).

tff(c_506,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_498])).

tff(c_110133,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110128,c_506])).

tff(c_110137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_110133])).

tff(c_110138,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_110387,plain,(
    ! [A_1021,B_1022,C_1023] :
      ( k7_subset_1(A_1021,B_1022,C_1023) = k4_xboole_0(B_1022,C_1023)
      | ~ m1_subset_1(B_1022,k1_zfmisc_1(A_1021)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110398,plain,(
    ! [C_1023] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_1023) = k4_xboole_0('#skF_3',C_1023) ),
    inference(resolution,[status(thm)],[c_54,c_110387])).

tff(c_111383,plain,(
    ! [A_1080,B_1081] :
      ( k7_subset_1(u1_struct_0(A_1080),B_1081,k2_tops_1(A_1080,B_1081)) = k1_tops_1(A_1080,B_1081)
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(u1_struct_0(A_1080)))
      | ~ l1_pre_topc(A_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_111402,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_111383])).

tff(c_111421,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_110398,c_111402])).

tff(c_110165,plain,(
    ! [B_991,A_992] :
      ( B_991 = A_992
      | ~ r1_tarski(B_991,A_992)
      | ~ r1_tarski(A_992,B_991) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110178,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_110165])).

tff(c_111442,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111421,c_110178])).

tff(c_111453,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111421,c_111442])).

tff(c_111484,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_111453])).

tff(c_110139,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_111799,plain,(
    ! [B_1090,A_1091,C_1092] :
      ( r1_tarski(B_1090,k1_tops_1(A_1091,C_1092))
      | ~ r1_tarski(B_1090,C_1092)
      | ~ v3_pre_topc(B_1090,A_1091)
      | ~ m1_subset_1(C_1092,k1_zfmisc_1(u1_struct_0(A_1091)))
      | ~ m1_subset_1(B_1090,k1_zfmisc_1(u1_struct_0(A_1091)))
      | ~ l1_pre_topc(A_1091) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_111822,plain,(
    ! [B_1090] :
      ( r1_tarski(B_1090,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1090,'#skF_3')
      | ~ v3_pre_topc(B_1090,'#skF_2')
      | ~ m1_subset_1(B_1090,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_111799])).

tff(c_111886,plain,(
    ! [B_1093] :
      ( r1_tarski(B_1093,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1093,'#skF_3')
      | ~ v3_pre_topc(B_1093,'#skF_2')
      | ~ m1_subset_1(B_1093,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_111822])).

tff(c_111920,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_111886])).

tff(c_111938,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110139,c_6,c_111920])).

tff(c_111940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111484,c_111938])).

tff(c_111941,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_111453])).

tff(c_112103,plain,(
    ! [A_1098,B_1099] :
      ( k7_subset_1(u1_struct_0(A_1098),k2_pre_topc(A_1098,B_1099),k1_tops_1(A_1098,B_1099)) = k2_tops_1(A_1098,B_1099)
      | ~ m1_subset_1(B_1099,k1_zfmisc_1(u1_struct_0(A_1098)))
      | ~ l1_pre_topc(A_1098) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_112112,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_111941,c_112103])).

tff(c_112116,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_112112])).

tff(c_112118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110138,c_112116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:24:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.78/33.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.78/33.91  
% 43.78/33.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.78/33.92  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 43.78/33.92  
% 43.78/33.92  %Foreground sorts:
% 43.78/33.92  
% 43.78/33.92  
% 43.78/33.92  %Background operators:
% 43.78/33.92  
% 43.78/33.92  
% 43.78/33.92  %Foreground operators:
% 43.78/33.92  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 43.78/33.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.78/33.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 43.78/33.92  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 43.78/33.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 43.78/33.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 43.78/33.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 43.78/33.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.78/33.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 43.78/33.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 43.78/33.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 43.78/33.92  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 43.78/33.92  tff('#skF_2', type, '#skF_2': $i).
% 43.78/33.92  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 43.78/33.92  tff('#skF_3', type, '#skF_3': $i).
% 43.78/33.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 43.78/33.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.78/33.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.78/33.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 43.78/33.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.78/33.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.78/33.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 43.78/33.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 43.78/33.92  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 43.78/33.92  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 43.78/33.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 43.78/33.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 43.78/33.92  
% 43.88/33.94  tff(f_150, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 43.88/33.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 43.88/33.94  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 43.88/33.94  tff(f_95, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 43.88/33.94  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 43.88/33.94  tff(f_89, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 43.88/33.94  tff(f_72, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 43.88/33.94  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 43.88/33.94  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 43.88/33.94  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 43.88/33.94  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 43.88/33.94  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 43.88/33.94  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 43.88/33.94  tff(f_66, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 43.88/33.94  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 43.88/33.94  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 43.88/33.94  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 43.88/33.94  tff(f_103, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 43.88/33.94  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 43.88/33.94  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 43.88/33.94  tff(c_60, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 43.88/33.94  tff(c_82, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 43.88/33.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.88/33.94  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 43.88/33.94  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 43.88/33.94  tff(c_1123, plain, (![A_166, B_167]: (k4_subset_1(u1_struct_0(A_166), B_167, k2_tops_1(A_166, B_167))=k2_pre_topc(A_166, B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_131])).
% 43.88/33.94  tff(c_1138, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1123])).
% 43.88/33.94  tff(c_1151, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1138])).
% 43.88/33.94  tff(c_42, plain, (![A_39, B_40]: (m1_subset_1(k2_tops_1(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_95])).
% 43.88/33.94  tff(c_854, plain, (![A_148, B_149, C_150]: (m1_subset_1(k4_subset_1(A_148, B_149, C_150), k1_zfmisc_1(A_148)) | ~m1_subset_1(C_150, k1_zfmisc_1(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 43.88/33.94  tff(c_38, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 43.88/33.94  tff(c_1973, plain, (![A_187, B_188, C_189]: (r1_tarski(k4_subset_1(A_187, B_188, C_189), A_187) | ~m1_subset_1(C_189, k1_zfmisc_1(A_187)) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(resolution, [status(thm)], [c_854, c_38])).
% 43.88/33.94  tff(c_2002, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_1973])).
% 43.88/33.94  tff(c_2021, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2002])).
% 43.88/33.94  tff(c_2165, plain, (~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2021])).
% 43.88/33.94  tff(c_2168, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_2165])).
% 43.88/33.94  tff(c_2175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2168])).
% 43.88/33.94  tff(c_2177, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2021])).
% 43.88/33.94  tff(c_2348, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2177, c_38])).
% 43.88/33.94  tff(c_40, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_89])).
% 43.88/33.94  tff(c_1014, plain, (![A_158, B_159, C_160]: (k4_subset_1(A_158, B_159, C_160)=k2_xboole_0(B_159, C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(A_158)) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 43.88/33.94  tff(c_2615, plain, (![B_198, B_199, A_200]: (k4_subset_1(B_198, B_199, A_200)=k2_xboole_0(B_199, A_200) | ~m1_subset_1(B_199, k1_zfmisc_1(B_198)) | ~r1_tarski(A_200, B_198))), inference(resolution, [status(thm)], [c_40, c_1014])).
% 43.88/33.94  tff(c_2703, plain, (![A_201]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_201)=k2_xboole_0('#skF_3', A_201) | ~r1_tarski(A_201, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_2615])).
% 43.88/33.94  tff(c_2712, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2348, c_2703])).
% 43.88/33.94  tff(c_2803, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_2712])).
% 43.88/33.94  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 43.88/33.94  tff(c_2853, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2803, c_12])).
% 43.88/33.94  tff(c_2176, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2021])).
% 43.88/33.94  tff(c_322, plain, (![A_106, B_107, C_108]: (k7_subset_1(A_106, B_107, C_108)=k4_xboole_0(B_107, C_108) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 43.88/33.94  tff(c_332, plain, (![B_38, A_37, C_108]: (k7_subset_1(B_38, A_37, C_108)=k4_xboole_0(A_37, C_108) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_40, c_322])).
% 43.88/33.94  tff(c_2588, plain, (![C_197]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_197)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_197))), inference(resolution, [status(thm)], [c_2176, c_332])).
% 43.88/33.94  tff(c_66, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 43.88/33.94  tff(c_136, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82, c_66])).
% 43.88/33.94  tff(c_2598, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2588, c_136])).
% 43.88/33.94  tff(c_163, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k3_subset_1(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.88/33.94  tff(c_222, plain, (![B_92, A_93]: (k4_xboole_0(B_92, A_93)=k3_subset_1(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(resolution, [status(thm)], [c_40, c_163])).
% 43.88/33.94  tff(c_251, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), A_7)=k3_subset_1(k2_xboole_0(A_7, B_8), A_7))), inference(resolution, [status(thm)], [c_12, c_222])).
% 43.88/33.94  tff(c_2844, plain, (k3_subset_1(k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3')), '#skF_3')=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2803, c_251])).
% 43.88/33.94  tff(c_2859, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_2598, c_2844])).
% 43.88/33.94  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 43.88/33.94  tff(c_2885, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2859, c_18])).
% 43.88/33.94  tff(c_87564, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2885])).
% 43.88/33.94  tff(c_87567, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_87564])).
% 43.88/33.94  tff(c_87571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2853, c_87567])).
% 43.88/33.94  tff(c_87573, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2885])).
% 43.88/33.94  tff(c_309, plain, (![A_104, B_105]: (k3_subset_1(A_104, k3_subset_1(A_104, B_105))=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 43.88/33.94  tff(c_319, plain, (![B_38, A_37]: (k3_subset_1(B_38, k3_subset_1(B_38, A_37))=A_37 | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_40, c_309])).
% 43.88/33.94  tff(c_2879, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2859, c_319])).
% 43.88/33.94  tff(c_2890, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2853, c_2879])).
% 43.88/33.94  tff(c_333, plain, (![C_108]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_108)=k4_xboole_0('#skF_3', C_108))), inference(resolution, [status(thm)], [c_54, c_322])).
% 43.88/33.94  tff(c_1335, plain, (![A_169, B_170]: (k7_subset_1(u1_struct_0(A_169), B_170, k2_tops_1(A_169, B_170))=k1_tops_1(A_169, B_170) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_138])).
% 43.88/33.94  tff(c_1352, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1335])).
% 43.88/33.94  tff(c_1368, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_333, c_1352])).
% 43.88/33.94  tff(c_442, plain, (![B_115, A_116, C_117]: (k7_subset_1(B_115, A_116, C_117)=k4_xboole_0(A_116, C_117) | ~r1_tarski(A_116, B_115))), inference(resolution, [status(thm)], [c_40, c_322])).
% 43.88/33.94  tff(c_470, plain, (![A_7, B_8, C_117]: (k7_subset_1(k2_xboole_0(A_7, B_8), A_7, C_117)=k4_xboole_0(A_7, C_117))), inference(resolution, [status(thm)], [c_12, c_442])).
% 43.88/33.94  tff(c_2847, plain, (![C_117]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_117)=k4_xboole_0('#skF_3', C_117))), inference(superposition, [status(thm), theory('equality')], [c_2803, c_470])).
% 43.88/33.94  tff(c_28, plain, (![A_23]: (m1_subset_1('#skF_1'(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 43.88/33.94  tff(c_142, plain, (![A_81, B_82, C_83]: (k9_subset_1(A_81, B_82, B_82)=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 43.88/33.94  tff(c_151, plain, (![A_23, B_82]: (k9_subset_1(A_23, B_82, B_82)=B_82)), inference(resolution, [status(thm)], [c_28, c_142])).
% 43.88/33.94  tff(c_1483, plain, (![A_171, B_172, C_173]: (k9_subset_1(A_171, B_172, k3_subset_1(A_171, C_173))=k7_subset_1(A_171, B_172, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | ~m1_subset_1(B_172, k1_zfmisc_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 43.88/33.94  tff(c_8900, plain, (![A_336, B_337, B_338]: (k9_subset_1(A_336, B_337, k3_subset_1(A_336, k3_subset_1(A_336, B_338)))=k7_subset_1(A_336, B_337, k3_subset_1(A_336, B_338)) | ~m1_subset_1(B_337, k1_zfmisc_1(A_336)) | ~m1_subset_1(B_338, k1_zfmisc_1(A_336)))), inference(resolution, [status(thm)], [c_18, c_1483])).
% 43.88/33.94  tff(c_109921, plain, (![A_982, B_983]: (k7_subset_1(A_982, k3_subset_1(A_982, k3_subset_1(A_982, B_983)), k3_subset_1(A_982, B_983))=k3_subset_1(A_982, k3_subset_1(A_982, B_983)) | ~m1_subset_1(k3_subset_1(A_982, k3_subset_1(A_982, B_983)), k1_zfmisc_1(A_982)) | ~m1_subset_1(B_983, k1_zfmisc_1(A_982)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8900])).
% 43.88/33.94  tff(c_109977, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3'))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2859, c_109921])).
% 43.88/33.94  tff(c_110027, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_87573, c_87573, c_2890, c_1368, c_2859, c_2890, c_2859, c_2847, c_2890, c_2859, c_109977])).
% 43.88/33.94  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 43.88/33.94  tff(c_116, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.88/33.94  tff(c_129, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_116])).
% 43.88/33.94  tff(c_1389, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1368, c_129])).
% 43.88/33.94  tff(c_1400, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1368, c_1389])).
% 43.88/33.94  tff(c_1431, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1400])).
% 43.88/33.94  tff(c_110083, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110027, c_1431])).
% 43.88/33.94  tff(c_110127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_110083])).
% 43.88/33.94  tff(c_110128, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1400])).
% 43.88/33.94  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 43.88/33.94  tff(c_490, plain, (![A_123, B_124]: (v3_pre_topc(k1_tops_1(A_123, B_124), A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_103])).
% 43.88/33.94  tff(c_498, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_490])).
% 43.88/33.94  tff(c_506, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_498])).
% 43.88/33.94  tff(c_110133, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110128, c_506])).
% 43.88/33.94  tff(c_110137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_110133])).
% 43.88/33.94  tff(c_110138, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 43.88/33.94  tff(c_110387, plain, (![A_1021, B_1022, C_1023]: (k7_subset_1(A_1021, B_1022, C_1023)=k4_xboole_0(B_1022, C_1023) | ~m1_subset_1(B_1022, k1_zfmisc_1(A_1021)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 43.88/33.94  tff(c_110398, plain, (![C_1023]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_1023)=k4_xboole_0('#skF_3', C_1023))), inference(resolution, [status(thm)], [c_54, c_110387])).
% 43.88/33.94  tff(c_111383, plain, (![A_1080, B_1081]: (k7_subset_1(u1_struct_0(A_1080), B_1081, k2_tops_1(A_1080, B_1081))=k1_tops_1(A_1080, B_1081) | ~m1_subset_1(B_1081, k1_zfmisc_1(u1_struct_0(A_1080))) | ~l1_pre_topc(A_1080))), inference(cnfTransformation, [status(thm)], [f_138])).
% 43.88/33.94  tff(c_111402, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_111383])).
% 43.88/33.94  tff(c_111421, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_110398, c_111402])).
% 43.88/33.94  tff(c_110165, plain, (![B_991, A_992]: (B_991=A_992 | ~r1_tarski(B_991, A_992) | ~r1_tarski(A_992, B_991))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.88/33.94  tff(c_110178, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_110165])).
% 43.88/33.94  tff(c_111442, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_111421, c_110178])).
% 43.88/33.94  tff(c_111453, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111421, c_111442])).
% 43.88/33.94  tff(c_111484, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_111453])).
% 43.88/33.94  tff(c_110139, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 43.88/33.94  tff(c_111799, plain, (![B_1090, A_1091, C_1092]: (r1_tarski(B_1090, k1_tops_1(A_1091, C_1092)) | ~r1_tarski(B_1090, C_1092) | ~v3_pre_topc(B_1090, A_1091) | ~m1_subset_1(C_1092, k1_zfmisc_1(u1_struct_0(A_1091))) | ~m1_subset_1(B_1090, k1_zfmisc_1(u1_struct_0(A_1091))) | ~l1_pre_topc(A_1091))), inference(cnfTransformation, [status(thm)], [f_124])).
% 43.88/33.94  tff(c_111822, plain, (![B_1090]: (r1_tarski(B_1090, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1090, '#skF_3') | ~v3_pre_topc(B_1090, '#skF_2') | ~m1_subset_1(B_1090, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_111799])).
% 43.88/33.94  tff(c_111886, plain, (![B_1093]: (r1_tarski(B_1093, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1093, '#skF_3') | ~v3_pre_topc(B_1093, '#skF_2') | ~m1_subset_1(B_1093, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_111822])).
% 43.88/33.94  tff(c_111920, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_111886])).
% 43.88/33.94  tff(c_111938, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110139, c_6, c_111920])).
% 43.88/33.94  tff(c_111940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111484, c_111938])).
% 43.88/33.94  tff(c_111941, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_111453])).
% 43.88/33.94  tff(c_112103, plain, (![A_1098, B_1099]: (k7_subset_1(u1_struct_0(A_1098), k2_pre_topc(A_1098, B_1099), k1_tops_1(A_1098, B_1099))=k2_tops_1(A_1098, B_1099) | ~m1_subset_1(B_1099, k1_zfmisc_1(u1_struct_0(A_1098))) | ~l1_pre_topc(A_1098))), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.88/33.94  tff(c_112112, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_111941, c_112103])).
% 43.88/33.94  tff(c_112116, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_112112])).
% 43.88/33.94  tff(c_112118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110138, c_112116])).
% 43.88/33.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.88/33.94  
% 43.88/33.94  Inference rules
% 43.88/33.94  ----------------------
% 43.88/33.94  #Ref     : 0
% 43.88/33.94  #Sup     : 26053
% 43.88/33.94  #Fact    : 0
% 43.88/33.94  #Define  : 0
% 43.88/33.94  #Split   : 24
% 43.88/33.94  #Chain   : 0
% 43.88/33.94  #Close   : 0
% 43.88/33.94  
% 43.88/33.94  Ordering : KBO
% 43.88/33.94  
% 43.88/33.94  Simplification rules
% 43.88/33.94  ----------------------
% 43.88/33.94  #Subsume      : 875
% 43.88/33.94  #Demod        : 36167
% 43.88/33.94  #Tautology    : 10472
% 43.88/33.94  #SimpNegUnit  : 9
% 43.88/33.94  #BackRed      : 169
% 43.88/33.94  
% 43.88/33.94  #Partial instantiations: 0
% 43.88/33.94  #Strategies tried      : 1
% 43.88/33.94  
% 43.88/33.94  Timing (in seconds)
% 43.88/33.94  ----------------------
% 43.88/33.94  Preprocessing        : 0.35
% 43.88/33.94  Parsing              : 0.19
% 43.88/33.94  CNF conversion       : 0.02
% 43.88/33.94  Main loop            : 32.81
% 43.88/33.94  Inferencing          : 3.82
% 43.88/33.94  Reduction            : 20.11
% 43.88/33.94  Demodulation         : 18.18
% 43.88/33.94  BG Simplification    : 0.40
% 43.88/33.94  Subsumption          : 7.09
% 43.88/33.94  Abstraction          : 0.81
% 43.88/33.94  MUC search           : 0.00
% 43.88/33.94  Cooper               : 0.00
% 43.88/33.94  Total                : 33.21
% 43.88/33.94  Index Insertion      : 0.00
% 43.88/33.94  Index Deletion       : 0.00
% 43.88/33.94  Index Matching       : 0.00
% 43.88/33.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
