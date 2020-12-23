%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:42 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 108 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 203 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_167,plain,(
    ! [A_78,B_79,C_80] :
      ( k7_subset_1(A_78,B_79,C_80) = k4_xboole_0(B_79,C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_42,c_167])).

tff(c_468,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1(k7_subset_1(A_128,B_129,C_130),k1_zfmisc_1(A_128))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_476,plain,(
    ! [C_80] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_80),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_468])).

tff(c_481,plain,(
    ! [C_80] : m1_subset_1(k4_xboole_0('#skF_2',C_80),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_476])).

tff(c_36,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_tarski(k1_tops_1(A_34,B_38),k1_tops_1(A_34,C_40))
      | ~ r1_tarski(B_38,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_624,plain,(
    ! [A_157,B_158] :
      ( r1_tarski(k1_tops_1(A_157,B_158),B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_637,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_624])).

tff(c_653,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_637])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_667,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_653,c_12])).

tff(c_628,plain,(
    ! [C_80] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_80)),k4_xboole_0('#skF_2',C_80))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_481,c_624])).

tff(c_921,plain,(
    ! [C_178] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_178)),k4_xboole_0('#skF_2',C_178)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_628])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_xboole_0(A_66,B_67)
      | ~ r1_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_129,plain,(
    ! [A_16,B_67,C_68] : r1_xboole_0(k4_xboole_0(A_16,k2_xboole_0(B_67,C_68)),B_67) ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_145,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_xboole_0(A_72,C_73)
      | ~ r1_xboole_0(B_74,C_73)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_152,plain,(
    ! [A_72,B_67,A_16,C_68] :
      ( r1_xboole_0(A_72,B_67)
      | ~ r1_tarski(A_72,k4_xboole_0(A_16,k2_xboole_0(B_67,C_68))) ) ),
    inference(resolution,[status(thm)],[c_129,c_145])).

tff(c_1100,plain,(
    ! [B_192,C_193] : r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',k2_xboole_0(B_192,C_193))),B_192) ),
    inference(resolution,[status(thm)],[c_921,c_152])).

tff(c_1115,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_1100])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k4_xboole_0(B_19,C_20))
      | ~ r1_xboole_0(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_799,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1(k1_tops_1(A_163,B_164),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( k7_subset_1(A_24,B_25,C_26) = k4_xboole_0(B_25,C_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2623,plain,(
    ! [A_317,B_318,C_319] :
      ( k7_subset_1(u1_struct_0(A_317),k1_tops_1(A_317,B_318),C_319) = k4_xboole_0(k1_tops_1(A_317,B_318),C_319)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(resolution,[status(thm)],[c_799,c_28])).

tff(c_2638,plain,(
    ! [C_319] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_319) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_319)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_2623])).

tff(c_2657,plain,(
    ! [C_319] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_319) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_319) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2638])).

tff(c_38,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_174,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_38])).

tff(c_2807,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_174])).

tff(c_3633,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_2807])).

tff(c_3636,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_3633])).

tff(c_3639,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3636])).

tff(c_3642,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_481,c_42,c_3639])).

tff(c_3645,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_3642])).

tff(c_3649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.07  
% 5.65/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.08  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.65/2.08  
% 5.65/2.08  %Foreground sorts:
% 5.65/2.08  
% 5.65/2.08  
% 5.65/2.08  %Background operators:
% 5.65/2.08  
% 5.65/2.08  
% 5.65/2.08  %Foreground operators:
% 5.65/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.65/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.65/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.65/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.65/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.65/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.65/2.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.65/2.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.65/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.65/2.08  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.65/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.65/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.65/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.65/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.65/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.65/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.65/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.65/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.65/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.65/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.65/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.65/2.08  
% 5.88/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.88/2.09  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 5.88/2.09  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 5.88/2.09  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.88/2.09  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 5.88/2.09  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 5.88/2.09  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.88/2.09  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.88/2.09  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.88/2.09  tff(f_63, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.88/2.09  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.88/2.09  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 5.88/2.09  tff(f_87, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 5.88/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.09  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.88/2.09  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.09  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.09  tff(c_167, plain, (![A_78, B_79, C_80]: (k7_subset_1(A_78, B_79, C_80)=k4_xboole_0(B_79, C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.88/2.09  tff(c_172, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_42, c_167])).
% 5.88/2.09  tff(c_468, plain, (![A_128, B_129, C_130]: (m1_subset_1(k7_subset_1(A_128, B_129, C_130), k1_zfmisc_1(A_128)) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.88/2.09  tff(c_476, plain, (![C_80]: (m1_subset_1(k4_xboole_0('#skF_2', C_80), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_172, c_468])).
% 5.88/2.09  tff(c_481, plain, (![C_80]: (m1_subset_1(k4_xboole_0('#skF_2', C_80), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_476])).
% 5.88/2.09  tff(c_36, plain, (![A_34, B_38, C_40]: (r1_tarski(k1_tops_1(A_34, B_38), k1_tops_1(A_34, C_40)) | ~r1_tarski(B_38, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.88/2.09  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.09  tff(c_624, plain, (![A_157, B_158]: (r1_tarski(k1_tops_1(A_157, B_158), B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.88/2.09  tff(c_637, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_624])).
% 5.88/2.09  tff(c_653, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_637])).
% 5.88/2.09  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.88/2.09  tff(c_667, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_653, c_12])).
% 5.88/2.09  tff(c_628, plain, (![C_80]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_80)), k4_xboole_0('#skF_2', C_80)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_481, c_624])).
% 5.88/2.09  tff(c_921, plain, (![C_178]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_178)), k4_xboole_0('#skF_2', C_178)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_628])).
% 5.88/2.09  tff(c_22, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.88/2.09  tff(c_116, plain, (![A_66, B_67, C_68]: (r1_xboole_0(A_66, B_67) | ~r1_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.88/2.09  tff(c_129, plain, (![A_16, B_67, C_68]: (r1_xboole_0(k4_xboole_0(A_16, k2_xboole_0(B_67, C_68)), B_67))), inference(resolution, [status(thm)], [c_22, c_116])).
% 5.88/2.09  tff(c_145, plain, (![A_72, C_73, B_74]: (r1_xboole_0(A_72, C_73) | ~r1_xboole_0(B_74, C_73) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.88/2.09  tff(c_152, plain, (![A_72, B_67, A_16, C_68]: (r1_xboole_0(A_72, B_67) | ~r1_tarski(A_72, k4_xboole_0(A_16, k2_xboole_0(B_67, C_68))))), inference(resolution, [status(thm)], [c_129, c_145])).
% 5.88/2.09  tff(c_1100, plain, (![B_192, C_193]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', k2_xboole_0(B_192, C_193))), B_192))), inference(resolution, [status(thm)], [c_921, c_152])).
% 5.88/2.09  tff(c_1115, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_667, c_1100])).
% 5.88/2.09  tff(c_24, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k4_xboole_0(B_19, C_20)) | ~r1_xboole_0(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.88/2.09  tff(c_799, plain, (![A_163, B_164]: (m1_subset_1(k1_tops_1(A_163, B_164), k1_zfmisc_1(u1_struct_0(A_163))) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.88/2.09  tff(c_28, plain, (![A_24, B_25, C_26]: (k7_subset_1(A_24, B_25, C_26)=k4_xboole_0(B_25, C_26) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.88/2.09  tff(c_2623, plain, (![A_317, B_318, C_319]: (k7_subset_1(u1_struct_0(A_317), k1_tops_1(A_317, B_318), C_319)=k4_xboole_0(k1_tops_1(A_317, B_318), C_319) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(resolution, [status(thm)], [c_799, c_28])).
% 5.88/2.09  tff(c_2638, plain, (![C_319]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_319)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_319) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_2623])).
% 5.88/2.09  tff(c_2657, plain, (![C_319]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_319)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_319))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2638])).
% 5.88/2.09  tff(c_38, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.09  tff(c_174, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_38])).
% 5.88/2.09  tff(c_2807, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_174])).
% 5.88/2.09  tff(c_3633, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2807])).
% 5.88/2.09  tff(c_3636, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_3633])).
% 5.88/2.09  tff(c_3639, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3636])).
% 5.88/2.09  tff(c_3642, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_481, c_42, c_3639])).
% 5.88/2.09  tff(c_3645, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_3642])).
% 5.88/2.09  tff(c_3649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3645])).
% 5.88/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.09  
% 5.88/2.09  Inference rules
% 5.88/2.09  ----------------------
% 5.88/2.09  #Ref     : 0
% 5.88/2.09  #Sup     : 886
% 5.88/2.09  #Fact    : 0
% 5.88/2.09  #Define  : 0
% 5.88/2.09  #Split   : 5
% 5.88/2.09  #Chain   : 0
% 5.88/2.09  #Close   : 0
% 5.88/2.09  
% 5.88/2.09  Ordering : KBO
% 5.88/2.09  
% 5.88/2.09  Simplification rules
% 5.88/2.09  ----------------------
% 5.88/2.09  #Subsume      : 42
% 5.88/2.09  #Demod        : 304
% 5.88/2.09  #Tautology    : 272
% 5.88/2.09  #SimpNegUnit  : 0
% 5.88/2.09  #BackRed      : 2
% 5.88/2.09  
% 5.88/2.09  #Partial instantiations: 0
% 5.88/2.09  #Strategies tried      : 1
% 5.88/2.09  
% 5.88/2.09  Timing (in seconds)
% 5.88/2.09  ----------------------
% 5.88/2.10  Preprocessing        : 0.35
% 5.88/2.10  Parsing              : 0.18
% 5.88/2.10  CNF conversion       : 0.02
% 5.88/2.10  Main loop            : 1.01
% 5.88/2.10  Inferencing          : 0.30
% 5.88/2.10  Reduction            : 0.37
% 5.88/2.10  Demodulation         : 0.28
% 5.88/2.10  BG Simplification    : 0.04
% 5.88/2.10  Subsumption          : 0.24
% 5.88/2.10  Abstraction          : 0.04
% 5.88/2.10  MUC search           : 0.00
% 5.88/2.10  Cooper               : 0.00
% 5.88/2.10  Total                : 1.39
% 5.88/2.10  Index Insertion      : 0.00
% 5.88/2.10  Index Deletion       : 0.00
% 5.88/2.10  Index Matching       : 0.00
% 5.88/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
