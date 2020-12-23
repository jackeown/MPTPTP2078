%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:54 EST 2020

% Result     : Theorem 21.42s
% Output     : CNFRefutation 21.45s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 244 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_126,axiom,(
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

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_646,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(A_113,B_114) = k3_subset_1(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_654,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_646])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_837,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_26])).

tff(c_50,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_pre_topc(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_64,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1732,plain,(
    ! [A_187,B_188] :
      ( k2_pre_topc(A_187,B_188) = B_188
      | ~ v4_pre_topc(B_188,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1743,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1732])).

tff(c_1748,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1743])).

tff(c_3286,plain,(
    ! [A_243,B_244] :
      ( k9_subset_1(u1_struct_0(A_243),k2_pre_topc(A_243,B_244),k2_pre_topc(A_243,k3_subset_1(u1_struct_0(A_243),B_244))) = k2_tops_1(A_243,B_244)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3313,plain,
    ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_3286])).

tff(c_3317,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3313])).

tff(c_1630,plain,(
    ! [A_177,C_178,B_179] :
      ( k9_subset_1(A_177,C_178,B_179) = k9_subset_1(A_177,B_179,C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1702,plain,(
    ! [B_186] : k9_subset_1(u1_struct_0('#skF_2'),B_186,'#skF_3') = k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_186) ),
    inference(resolution,[status(thm)],[c_66,c_1630])).

tff(c_40,plain,(
    ! [A_36,B_37,C_38] :
      ( m1_subset_1(k9_subset_1(A_36,B_37,C_38),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1714,plain,(
    ! [B_186] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_186),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_40])).

tff(c_1724,plain,(
    ! [B_186] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_186),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1714])).

tff(c_80041,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3317,c_1724])).

tff(c_62,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    ! [A_43,B_44,C_46] :
      ( r1_tarski(k3_subset_1(A_43,B_44),k3_subset_1(A_43,k9_subset_1(A_43,B_44,C_46)))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2818,plain,(
    ! [B_229,C_230,A_231] :
      ( r1_tarski(B_229,C_230)
      | ~ r1_tarski(k3_subset_1(A_231,C_230),k3_subset_1(A_231,B_229))
      | ~ m1_subset_1(C_230,k1_zfmisc_1(A_231))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(A_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2836,plain,(
    ! [A_43,B_44,C_46] :
      ( r1_tarski(k9_subset_1(A_43,B_44,C_46),B_44)
      | ~ m1_subset_1(k9_subset_1(A_43,B_44,C_46),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2818])).

tff(c_80069,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))),'#skF_3')
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3317,c_2836])).

tff(c_80094,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3317,c_80069])).

tff(c_80095,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_80094])).

tff(c_80470,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80041,c_80095])).

tff(c_80473,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_80470])).

tff(c_80479,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_80473])).

tff(c_80484,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_80479])).

tff(c_80488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_80484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:59:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.42/13.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.42/13.38  
% 21.42/13.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.45/13.38  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 21.45/13.38  
% 21.45/13.38  %Foreground sorts:
% 21.45/13.38  
% 21.45/13.38  
% 21.45/13.38  %Background operators:
% 21.45/13.38  
% 21.45/13.38  
% 21.45/13.38  %Foreground operators:
% 21.45/13.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.45/13.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.45/13.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.45/13.38  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 21.45/13.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.45/13.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.45/13.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.45/13.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.45/13.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.45/13.38  tff('#skF_2', type, '#skF_2': $i).
% 21.45/13.38  tff('#skF_3', type, '#skF_3': $i).
% 21.45/13.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.45/13.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 21.45/13.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.45/13.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.45/13.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.45/13.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.45/13.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.45/13.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.45/13.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.45/13.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 21.45/13.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.45/13.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.45/13.38  
% 21.45/13.40  tff(f_143, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 21.45/13.40  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 21.45/13.40  tff(f_56, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.45/13.40  tff(f_100, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.45/13.40  tff(f_111, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 21.45/13.40  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 21.45/13.40  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 21.45/13.40  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 21.45/13.40  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 21.45/13.40  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 21.45/13.40  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 21.45/13.40  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 21.45/13.40  tff(c_646, plain, (![A_113, B_114]: (k4_xboole_0(A_113, B_114)=k3_subset_1(A_113, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 21.45/13.40  tff(c_654, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_646])).
% 21.45/13.40  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.45/13.40  tff(c_837, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_654, c_26])).
% 21.45/13.40  tff(c_50, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_100])).
% 21.45/13.40  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 21.45/13.40  tff(c_54, plain, (![A_51, B_52]: (m1_subset_1(k2_pre_topc(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_111])).
% 21.45/13.40  tff(c_64, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 21.45/13.40  tff(c_1732, plain, (![A_187, B_188]: (k2_pre_topc(A_187, B_188)=B_188 | ~v4_pre_topc(B_188, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_126])).
% 21.45/13.40  tff(c_1743, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1732])).
% 21.45/13.40  tff(c_1748, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1743])).
% 21.45/13.40  tff(c_3286, plain, (![A_243, B_244]: (k9_subset_1(u1_struct_0(A_243), k2_pre_topc(A_243, B_244), k2_pre_topc(A_243, k3_subset_1(u1_struct_0(A_243), B_244)))=k2_tops_1(A_243, B_244) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_133])).
% 21.45/13.40  tff(c_3313, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1748, c_3286])).
% 21.45/13.40  tff(c_3317, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3313])).
% 21.45/13.40  tff(c_1630, plain, (![A_177, C_178, B_179]: (k9_subset_1(A_177, C_178, B_179)=k9_subset_1(A_177, B_179, C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.45/13.40  tff(c_1702, plain, (![B_186]: (k9_subset_1(u1_struct_0('#skF_2'), B_186, '#skF_3')=k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_186))), inference(resolution, [status(thm)], [c_66, c_1630])).
% 21.45/13.40  tff(c_40, plain, (![A_36, B_37, C_38]: (m1_subset_1(k9_subset_1(A_36, B_37, C_38), k1_zfmisc_1(A_36)) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 21.45/13.40  tff(c_1714, plain, (![B_186]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_186), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1702, c_40])).
% 21.45/13.40  tff(c_1724, plain, (![B_186]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_186), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1714])).
% 21.45/13.40  tff(c_80041, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3317, c_1724])).
% 21.45/13.40  tff(c_62, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 21.45/13.40  tff(c_46, plain, (![A_43, B_44, C_46]: (r1_tarski(k3_subset_1(A_43, B_44), k3_subset_1(A_43, k9_subset_1(A_43, B_44, C_46))) | ~m1_subset_1(C_46, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.45/13.40  tff(c_2818, plain, (![B_229, C_230, A_231]: (r1_tarski(B_229, C_230) | ~r1_tarski(k3_subset_1(A_231, C_230), k3_subset_1(A_231, B_229)) | ~m1_subset_1(C_230, k1_zfmisc_1(A_231)) | ~m1_subset_1(B_229, k1_zfmisc_1(A_231)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.45/13.40  tff(c_2836, plain, (![A_43, B_44, C_46]: (r1_tarski(k9_subset_1(A_43, B_44, C_46), B_44) | ~m1_subset_1(k9_subset_1(A_43, B_44, C_46), k1_zfmisc_1(A_43)) | ~m1_subset_1(C_46, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_46, c_2818])).
% 21.45/13.40  tff(c_80069, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), '#skF_3') | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3317, c_2836])).
% 21.45/13.40  tff(c_80094, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3317, c_80069])).
% 21.45/13.40  tff(c_80095, plain, (~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_80094])).
% 21.45/13.40  tff(c_80470, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80041, c_80095])).
% 21.45/13.40  tff(c_80473, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_80470])).
% 21.45/13.40  tff(c_80479, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_80473])).
% 21.45/13.40  tff(c_80484, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_80479])).
% 21.45/13.40  tff(c_80488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_837, c_80484])).
% 21.45/13.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.45/13.40  
% 21.45/13.40  Inference rules
% 21.45/13.40  ----------------------
% 21.45/13.40  #Ref     : 0
% 21.45/13.40  #Sup     : 19243
% 21.45/13.40  #Fact    : 0
% 21.45/13.40  #Define  : 0
% 21.45/13.40  #Split   : 4
% 21.45/13.40  #Chain   : 0
% 21.45/13.40  #Close   : 0
% 21.45/13.40  
% 21.45/13.40  Ordering : KBO
% 21.45/13.40  
% 21.45/13.40  Simplification rules
% 21.45/13.40  ----------------------
% 21.45/13.40  #Subsume      : 1418
% 21.45/13.40  #Demod        : 19750
% 21.45/13.40  #Tautology    : 12075
% 21.45/13.40  #SimpNegUnit  : 1
% 21.45/13.40  #BackRed      : 2
% 21.45/13.40  
% 21.45/13.40  #Partial instantiations: 0
% 21.45/13.40  #Strategies tried      : 1
% 21.45/13.40  
% 21.45/13.40  Timing (in seconds)
% 21.45/13.40  ----------------------
% 21.45/13.40  Preprocessing        : 0.36
% 21.45/13.40  Parsing              : 0.19
% 21.45/13.40  CNF conversion       : 0.02
% 21.45/13.40  Main loop            : 12.23
% 21.45/13.40  Inferencing          : 1.31
% 21.45/13.40  Reduction            : 7.86
% 21.45/13.40  Demodulation         : 7.19
% 21.45/13.40  BG Simplification    : 0.15
% 21.45/13.40  Subsumption          : 2.45
% 21.45/13.40  Abstraction          : 0.26
% 21.45/13.40  MUC search           : 0.00
% 21.45/13.40  Cooper               : 0.00
% 21.45/13.40  Total                : 12.61
% 21.45/13.40  Index Insertion      : 0.00
% 21.45/13.40  Index Deletion       : 0.00
% 21.45/13.40  Index Matching       : 0.00
% 21.45/13.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
