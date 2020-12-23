%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 23.80s
% Output     : CNFRefutation 23.94s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 203 expanded)
%              Number of leaves         :   35 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 415 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
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

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_60,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3150,plain,(
    ! [A_243,C_244,B_245] :
      ( r1_tarski(k2_pre_topc(A_243,C_244),B_245)
      | ~ r1_tarski(C_244,B_245)
      | ~ v4_pre_topc(B_245,A_243)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3165,plain,(
    ! [B_245] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_245)
      | ~ r1_tarski('#skF_2',B_245)
      | ~ v4_pre_topc(B_245,'#skF_1')
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_3150])).

tff(c_7073,plain,(
    ! [B_311] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_311)
      | ~ r1_tarski('#skF_2',B_311)
      | ~ v4_pre_topc(B_311,'#skF_1')
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3165])).

tff(c_7103,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_7073])).

tff(c_7119,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6,c_7103])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7133,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7119,c_2])).

tff(c_50517,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7133])).

tff(c_2537,plain,(
    ! [A_218,B_219] :
      ( k4_subset_1(u1_struct_0(A_218),B_219,k2_tops_1(A_218,B_219)) = k2_pre_topc(A_218,B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2550,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2537])).

tff(c_2557,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2550])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k3_subset_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2312,plain,(
    ! [A_214,B_215] :
      ( k2_tops_1(A_214,k3_subset_1(u1_struct_0(A_214),B_215)) = k2_tops_1(A_214,B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2325,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2312])).

tff(c_2332,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2325])).

tff(c_1446,plain,(
    ! [A_167,B_168] :
      ( m1_subset_1(k2_tops_1(A_167,B_168),k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6848,plain,(
    ! [A_304,B_305] :
      ( r1_tarski(k2_tops_1(A_304,B_305),u1_struct_0(A_304))
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0(A_304)))
      | ~ l1_pre_topc(A_304) ) ),
    inference(resolution,[status(thm)],[c_1446,c_48])).

tff(c_6865,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2332,c_6848])).

tff(c_6874,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6865])).

tff(c_68611,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6874])).

tff(c_68614,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_68611])).

tff(c_68621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68614])).

tff(c_68622,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6874])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1952,plain,(
    ! [A_201,B_202,C_203] :
      ( k4_subset_1(A_201,B_202,C_203) = k2_xboole_0(B_202,C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_201))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14464,plain,(
    ! [B_403,B_404,A_405] :
      ( k4_subset_1(B_403,B_404,A_405) = k2_xboole_0(B_404,A_405)
      | ~ m1_subset_1(B_404,k1_zfmisc_1(B_403))
      | ~ r1_tarski(A_405,B_403) ) ),
    inference(resolution,[status(thm)],[c_50,c_1952])).

tff(c_14489,plain,(
    ! [A_405] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_405) = k2_xboole_0('#skF_2',A_405)
      | ~ r1_tarski(A_405,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_64,c_14464])).

tff(c_68635,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68622,c_14489])).

tff(c_68657,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_68635])).

tff(c_28,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69396,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68657,c_28])).

tff(c_69410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50517,c_69396])).

tff(c_69411,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7133])).

tff(c_69437,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69411,c_2557])).

tff(c_88770,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6874])).

tff(c_88773,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_88770])).

tff(c_88780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88773])).

tff(c_88781,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6874])).

tff(c_88794,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88781,c_14489])).

tff(c_88816,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69437,c_88794])).

tff(c_30,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_147,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_616,plain,(
    ! [A_114,B_115] : k3_tarski(k2_tarski(A_114,B_115)) = k2_xboole_0(B_115,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_147])).

tff(c_32,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_639,plain,(
    ! [B_116,A_117] : k2_xboole_0(B_116,A_117) = k2_xboole_0(A_117,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_32])).

tff(c_654,plain,(
    ! [A_117,B_116] : r1_tarski(A_117,k2_xboole_0(B_116,A_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_28])).

tff(c_89003,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88816,c_654])).

tff(c_89040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_89003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.80/15.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/15.21  
% 23.94/15.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/15.21  %$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 23.94/15.21  
% 23.94/15.21  %Foreground sorts:
% 23.94/15.21  
% 23.94/15.21  
% 23.94/15.21  %Background operators:
% 23.94/15.21  
% 23.94/15.21  
% 23.94/15.21  %Foreground operators:
% 23.94/15.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.94/15.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.94/15.21  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 23.94/15.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.94/15.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.94/15.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.94/15.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.94/15.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.94/15.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.94/15.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.94/15.21  tff('#skF_2', type, '#skF_2': $i).
% 23.94/15.21  tff('#skF_1', type, '#skF_1': $i).
% 23.94/15.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.94/15.21  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.94/15.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.94/15.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.94/15.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.94/15.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.94/15.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.94/15.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.94/15.21  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.94/15.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.94/15.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.94/15.21  
% 23.94/15.23  tff(f_153, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 23.94/15.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.94/15.23  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 23.94/15.23  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 23.94/15.23  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 23.94/15.23  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 23.94/15.23  tff(f_115, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 23.94/15.23  tff(f_109, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 23.94/15.23  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.94/15.23  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 23.94/15.23  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 23.94/15.23  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 23.94/15.23  tff(c_60, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 23.94/15.23  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 23.94/15.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.94/15.23  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 23.94/15.23  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 23.94/15.23  tff(c_3150, plain, (![A_243, C_244, B_245]: (r1_tarski(k2_pre_topc(A_243, C_244), B_245) | ~r1_tarski(C_244, B_245) | ~v4_pre_topc(B_245, A_243) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.94/15.23  tff(c_3165, plain, (![B_245]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_245) | ~r1_tarski('#skF_2', B_245) | ~v4_pre_topc(B_245, '#skF_1') | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_3150])).
% 23.94/15.23  tff(c_7073, plain, (![B_311]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_311) | ~r1_tarski('#skF_2', B_311) | ~v4_pre_topc(B_311, '#skF_1') | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3165])).
% 23.94/15.23  tff(c_7103, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_7073])).
% 23.94/15.23  tff(c_7119, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6, c_7103])).
% 23.94/15.23  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.94/15.23  tff(c_7133, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_7119, c_2])).
% 23.94/15.23  tff(c_50517, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7133])).
% 23.94/15.23  tff(c_2537, plain, (![A_218, B_219]: (k4_subset_1(u1_struct_0(A_218), B_219, k2_tops_1(A_218, B_219))=k2_pre_topc(A_218, B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.94/15.23  tff(c_2550, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_2537])).
% 23.94/15.23  tff(c_2557, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2550])).
% 23.94/15.23  tff(c_36, plain, (![A_32, B_33]: (m1_subset_1(k3_subset_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.94/15.23  tff(c_2312, plain, (![A_214, B_215]: (k2_tops_1(A_214, k3_subset_1(u1_struct_0(A_214), B_215))=k2_tops_1(A_214, B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_136])).
% 23.94/15.23  tff(c_2325, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_2312])).
% 23.94/15.23  tff(c_2332, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2325])).
% 23.94/15.23  tff(c_1446, plain, (![A_167, B_168]: (m1_subset_1(k2_tops_1(A_167, B_168), k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_115])).
% 23.94/15.23  tff(c_48, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.94/15.23  tff(c_6848, plain, (![A_304, B_305]: (r1_tarski(k2_tops_1(A_304, B_305), u1_struct_0(A_304)) | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0(A_304))) | ~l1_pre_topc(A_304))), inference(resolution, [status(thm)], [c_1446, c_48])).
% 23.94/15.23  tff(c_6865, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2332, c_6848])).
% 23.94/15.23  tff(c_6874, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6865])).
% 23.94/15.23  tff(c_68611, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_6874])).
% 23.94/15.23  tff(c_68614, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_68611])).
% 23.94/15.23  tff(c_68621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68614])).
% 23.94/15.23  tff(c_68622, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_6874])).
% 23.94/15.23  tff(c_50, plain, (![A_50, B_51]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.94/15.23  tff(c_1952, plain, (![A_201, B_202, C_203]: (k4_subset_1(A_201, B_202, C_203)=k2_xboole_0(B_202, C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(A_201)) | ~m1_subset_1(B_202, k1_zfmisc_1(A_201)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 23.94/15.23  tff(c_14464, plain, (![B_403, B_404, A_405]: (k4_subset_1(B_403, B_404, A_405)=k2_xboole_0(B_404, A_405) | ~m1_subset_1(B_404, k1_zfmisc_1(B_403)) | ~r1_tarski(A_405, B_403))), inference(resolution, [status(thm)], [c_50, c_1952])).
% 23.94/15.23  tff(c_14489, plain, (![A_405]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_405)=k2_xboole_0('#skF_2', A_405) | ~r1_tarski(A_405, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_64, c_14464])).
% 23.94/15.23  tff(c_68635, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68622, c_14489])).
% 23.94/15.23  tff(c_68657, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_68635])).
% 23.94/15.23  tff(c_28, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.94/15.23  tff(c_69396, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68657, c_28])).
% 23.94/15.23  tff(c_69410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50517, c_69396])).
% 23.94/15.23  tff(c_69411, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_7133])).
% 23.94/15.23  tff(c_69437, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_69411, c_2557])).
% 23.94/15.23  tff(c_88770, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_6874])).
% 23.94/15.23  tff(c_88773, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_88770])).
% 23.94/15.23  tff(c_88780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_88773])).
% 23.94/15.23  tff(c_88781, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_6874])).
% 23.94/15.23  tff(c_88794, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88781, c_14489])).
% 23.94/15.23  tff(c_88816, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_69437, c_88794])).
% 23.94/15.23  tff(c_30, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.94/15.23  tff(c_147, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.94/15.23  tff(c_616, plain, (![A_114, B_115]: (k3_tarski(k2_tarski(A_114, B_115))=k2_xboole_0(B_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_30, c_147])).
% 23.94/15.23  tff(c_32, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.94/15.23  tff(c_639, plain, (![B_116, A_117]: (k2_xboole_0(B_116, A_117)=k2_xboole_0(A_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_616, c_32])).
% 23.94/15.23  tff(c_654, plain, (![A_117, B_116]: (r1_tarski(A_117, k2_xboole_0(B_116, A_117)))), inference(superposition, [status(thm), theory('equality')], [c_639, c_28])).
% 23.94/15.23  tff(c_89003, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88816, c_654])).
% 23.94/15.23  tff(c_89040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_89003])).
% 23.94/15.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/15.23  
% 23.94/15.23  Inference rules
% 23.94/15.23  ----------------------
% 23.94/15.23  #Ref     : 0
% 23.94/15.23  #Sup     : 21341
% 23.94/15.23  #Fact    : 0
% 23.94/15.23  #Define  : 0
% 23.94/15.23  #Split   : 8
% 23.94/15.23  #Chain   : 0
% 23.94/15.23  #Close   : 0
% 23.94/15.23  
% 23.94/15.23  Ordering : KBO
% 23.94/15.23  
% 23.94/15.23  Simplification rules
% 23.94/15.23  ----------------------
% 23.94/15.23  #Subsume      : 1543
% 23.94/15.23  #Demod        : 23057
% 23.94/15.23  #Tautology    : 11706
% 23.94/15.23  #SimpNegUnit  : 2
% 23.94/15.23  #BackRed      : 36
% 23.94/15.23  
% 23.94/15.23  #Partial instantiations: 0
% 23.94/15.23  #Strategies tried      : 1
% 23.94/15.23  
% 23.94/15.23  Timing (in seconds)
% 23.94/15.23  ----------------------
% 23.94/15.23  Preprocessing        : 0.36
% 23.94/15.23  Parsing              : 0.20
% 23.94/15.23  CNF conversion       : 0.02
% 23.94/15.23  Main loop            : 14.07
% 23.94/15.23  Inferencing          : 1.57
% 23.94/15.23  Reduction            : 8.54
% 23.94/15.23  Demodulation         : 7.71
% 23.94/15.23  BG Simplification    : 0.18
% 23.94/15.23  Subsumption          : 3.20
% 23.94/15.23  Abstraction          : 0.31
% 23.94/15.23  MUC search           : 0.00
% 23.94/15.23  Cooper               : 0.00
% 23.94/15.23  Total                : 14.47
% 23.94/15.23  Index Insertion      : 0.00
% 23.94/15.23  Index Deletion       : 0.00
% 23.94/15.23  Index Matching       : 0.00
% 23.94/15.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
