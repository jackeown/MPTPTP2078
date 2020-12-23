%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1244+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:38 EST 2020

% Result     : Theorem 9.76s
% Output     : CNFRefutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :   88 (1262 expanded)
%              Number of leaves         :   22 ( 434 expanded)
%              Depth                    :   17
%              Number of atoms          :  212 (3042 expanded)
%              Number of equality atoms :   28 ( 642 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) != k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tops_1(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_43,B_44] :
      ( k1_tops_1(A_43,k1_tops_1(A_43,B_44)) = k1_tops_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_83,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_65,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tops_1(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( r1_tarski(B_16,k2_pre_topc(A_14,B_16))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_128,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tops_1(A_50,B_51),k2_pre_topc(A_50,k1_tops_1(A_50,B_51)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_65,c_18])).

tff(c_133,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_128])).

tff(c_139,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_83,c_133])).

tff(c_278,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_281,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_278])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_281])).

tff(c_287,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_pre_topc(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_pre_topc(A_9,k2_pre_topc(A_9,B_10)) = k2_pre_topc(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_289,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_287,c_14])).

tff(c_298,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_289])).

tff(c_58,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_pre_topc(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_tops_1(A_11,B_13),B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tops_1(A_39,k2_pre_topc(A_39,B_40)),k2_pre_topc(A_39,B_40))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_58,c_16])).

tff(c_351,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_63])).

tff(c_372,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_298,c_351])).

tff(c_607,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_610,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_607])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_287,c_610])).

tff(c_616,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_535,plain,(
    ! [A_73,B_74] :
      ( k1_tops_1(A_73,k1_tops_1(A_73,k2_pre_topc(A_73,B_74))) = k1_tops_1(A_73,k2_pre_topc(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_537,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_287,c_535])).

tff(c_548,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_537])).

tff(c_308,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k1_tops_1(A_61,B_62),k1_tops_1(A_61,C_63))
      | ~ r1_tarski(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_322,plain,(
    ! [B_62] :
      ( r1_tarski(k1_tops_1('#skF_1',B_62),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_62,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_308])).

tff(c_331,plain,(
    ! [B_62] :
      ( r1_tarski(k1_tops_1('#skF_1',B_62),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_62,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_287,c_322])).

tff(c_22,plain,(
    ! [A_24,B_28,C_30] :
      ( r1_tarski(k2_pre_topc(A_24,B_28),k2_pre_topc(A_24,C_30))
      | ~ r1_tarski(B_28,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_114,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k2_pre_topc(A_47,B_48),k2_pre_topc(A_47,C_49))
      | ~ r1_tarski(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_836,plain,(
    ! [A_81,C_82,B_83] :
      ( k2_pre_topc(A_81,C_82) = k2_pre_topc(A_81,B_83)
      | ~ r1_tarski(k2_pre_topc(A_81,C_82),k2_pre_topc(A_81,B_83))
      | ~ r1_tarski(B_83,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_2715,plain,(
    ! [A_116,C_117,B_118] :
      ( k2_pre_topc(A_116,C_117) = k2_pre_topc(A_116,B_118)
      | ~ r1_tarski(C_117,B_118)
      | ~ r1_tarski(B_118,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_22,c_836])).

tff(c_3492,plain,(
    ! [A_134,B_135] :
      ( k2_pre_topc(A_134,k1_tops_1('#skF_1',B_135)) = k2_pre_topc(A_134,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',B_135))
      | ~ m1_subset_1(k1_tops_1('#skF_1',B_135),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ r1_tarski(B_135,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_331,c_2715])).

tff(c_3519,plain,(
    ! [B_4] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',B_4)) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',B_4))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_4,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_3492])).

tff(c_4777,plain,(
    ! [B_162] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',B_162)) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',B_162))
      | ~ r1_tarski(B_162,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_287,c_3519])).

tff(c_4802,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_4777])).

tff(c_4836,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_4802])).

tff(c_4837,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_4836])).

tff(c_4852,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4837])).

tff(c_4855,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_4852])).

tff(c_4859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_616,c_4855])).

tff(c_4861,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4837])).

tff(c_286,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_319,plain,(
    ! [C_63] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_63))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_308])).

tff(c_329,plain,(
    ! [C_63] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',C_63))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_287,c_319])).

tff(c_4860,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_4837])).

tff(c_4999,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_4860])).

tff(c_5002,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_329,c_4999])).

tff(c_5009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_286,c_5002])).

tff(c_5011,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_4860])).

tff(c_615,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_848,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',B_83)
      | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',B_83))
      | ~ r1_tarski(B_83,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_836])).

tff(c_9777,plain,(
    ! [B_224] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',B_224)
      | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',B_224))
      | ~ r1_tarski(B_224,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_616,c_298,c_848])).

tff(c_9817,plain,(
    ! [C_30] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',C_30)
      | ~ r1_tarski(C_30,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_9777])).

tff(c_9855,plain,(
    ! [C_225] :
      ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',C_225)
      | ~ r1_tarski(C_225,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_287,c_9817])).

tff(c_9858,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_615,c_9855])).

tff(c_9884,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4861,c_5011,c_9858])).

tff(c_9886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_9884])).

%------------------------------------------------------------------------------
