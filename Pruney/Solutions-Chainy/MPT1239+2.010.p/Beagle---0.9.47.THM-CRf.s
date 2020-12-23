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
% DateTime   : Thu Dec  3 10:20:42 EST 2020

% Result     : Theorem 21.46s
% Output     : CNFRefutation 21.46s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 131 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 270 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k4_xboole_0(A_6,C_8),B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_387,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_tops_1(A_100,B_101),B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_416,plain,(
    ! [A_102,A_103] :
      ( r1_tarski(k1_tops_1(A_102,A_103),A_103)
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(A_103,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_24,c_387])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_438,plain,(
    ! [A_102,B_4,C_5] :
      ( r1_xboole_0(k1_tops_1(A_102,k4_xboole_0(B_4,C_5)),C_5)
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(k4_xboole_0(B_4,C_5),u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_416,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k4_xboole_0(B_16,C_17))
      | ~ r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_394,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_387])).

tff(c_401,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_394])).

tff(c_97,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_xboole_0(A_54,C_55)
      | ~ r1_tarski(A_54,k4_xboole_0(B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_56,C_55] : r1_xboole_0(k4_xboole_0(B_56,C_55),C_55) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_450,plain,(
    ! [A_105,C_106,B_107,D_108] :
      ( r1_xboole_0(A_105,C_106)
      | ~ r1_xboole_0(B_107,D_108)
      | ~ r1_tarski(C_106,D_108)
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_469,plain,(
    ! [A_110,C_111,C_112,B_113] :
      ( r1_xboole_0(A_110,C_111)
      | ~ r1_tarski(C_111,C_112)
      | ~ r1_tarski(A_110,k4_xboole_0(B_113,C_112)) ) ),
    inference(resolution,[status(thm)],[c_112,c_450])).

tff(c_645,plain,(
    ! [A_124,B_125] :
      ( r1_xboole_0(A_124,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_124,k4_xboole_0(B_125,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_401,c_469])).

tff(c_4744,plain,(
    ! [A_301,B_302] :
      ( r1_xboole_0(A_301,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_301,'#skF_3')
      | ~ r1_tarski(A_301,B_302) ) ),
    inference(resolution,[status(thm)],[c_18,c_645])).

tff(c_4789,plain,(
    ! [B_2] :
      ( r1_xboole_0(B_2,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(B_2,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_4744])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_677,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1(k1_tops_1(A_126,B_127),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( k7_subset_1(A_18,B_19,C_20) = k4_xboole_0(B_19,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3630,plain,(
    ! [A_255,B_256,C_257] :
      ( k7_subset_1(u1_struct_0(A_255),k1_tops_1(A_255,B_256),C_257) = k4_xboole_0(k1_tops_1(A_255,B_256),C_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_677,c_20])).

tff(c_3637,plain,(
    ! [C_257] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_257) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_257)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_3630])).

tff(c_3644,plain,(
    ! [C_257] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_257) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_257) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3637])).

tff(c_294,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_302,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_36,c_294])).

tff(c_32,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_304,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_32])).

tff(c_3681,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3644,c_304])).

tff(c_4743,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_3681])).

tff(c_69750,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4743])).

tff(c_69753,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_69750])).

tff(c_69756,plain,(
    ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_14,c_69753])).

tff(c_69760,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_69756])).

tff(c_69763,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_69760])).

tff(c_69767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_69763])).

tff(c_69768,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4743])).

tff(c_70194,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4789,c_69768])).

tff(c_70197,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_438,c_70194])).

tff(c_70200,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70197])).

tff(c_70203,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_70200])).

tff(c_70207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_70203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:04:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.46/12.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.46/12.46  
% 21.46/12.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.46/12.46  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 21.46/12.46  
% 21.46/12.46  %Foreground sorts:
% 21.46/12.46  
% 21.46/12.46  
% 21.46/12.46  %Background operators:
% 21.46/12.46  
% 21.46/12.46  
% 21.46/12.46  %Foreground operators:
% 21.46/12.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.46/12.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.46/12.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.46/12.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.46/12.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 21.46/12.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.46/12.46  tff('#skF_2', type, '#skF_2': $i).
% 21.46/12.46  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 21.46/12.46  tff('#skF_3', type, '#skF_3': $i).
% 21.46/12.46  tff('#skF_1', type, '#skF_1': $i).
% 21.46/12.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.46/12.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.46/12.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.46/12.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.46/12.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.46/12.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.46/12.46  
% 21.46/12.47  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 21.46/12.47  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.46/12.47  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 21.46/12.47  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 21.46/12.47  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 21.46/12.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.46/12.47  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 21.46/12.47  tff(f_51, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 21.46/12.47  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.46/12.47  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 21.46/12.47  tff(f_71, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 21.46/12.47  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 21.46/12.47  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.46/12.47  tff(c_44, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.46/12.47  tff(c_51, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_44])).
% 21.46/12.47  tff(c_12, plain, (![A_6, C_8, B_7]: (r1_tarski(k4_xboole_0(A_6, C_8), B_7) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.46/12.47  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.46/12.47  tff(c_24, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.46/12.47  tff(c_387, plain, (![A_100, B_101]: (r1_tarski(k1_tops_1(A_100, B_101), B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 21.46/12.47  tff(c_416, plain, (![A_102, A_103]: (r1_tarski(k1_tops_1(A_102, A_103), A_103) | ~l1_pre_topc(A_102) | ~r1_tarski(A_103, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_24, c_387])).
% 21.46/12.47  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.46/12.47  tff(c_438, plain, (![A_102, B_4, C_5]: (r1_xboole_0(k1_tops_1(A_102, k4_xboole_0(B_4, C_5)), C_5) | ~l1_pre_topc(A_102) | ~r1_tarski(k4_xboole_0(B_4, C_5), u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_416, c_8])).
% 21.46/12.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.46/12.47  tff(c_18, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k4_xboole_0(B_16, C_17)) | ~r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 21.46/12.47  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.46/12.47  tff(c_394, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_387])).
% 21.46/12.47  tff(c_401, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_394])).
% 21.46/12.47  tff(c_97, plain, (![A_54, C_55, B_56]: (r1_xboole_0(A_54, C_55) | ~r1_tarski(A_54, k4_xboole_0(B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.46/12.47  tff(c_112, plain, (![B_56, C_55]: (r1_xboole_0(k4_xboole_0(B_56, C_55), C_55))), inference(resolution, [status(thm)], [c_6, c_97])).
% 21.46/12.47  tff(c_450, plain, (![A_105, C_106, B_107, D_108]: (r1_xboole_0(A_105, C_106) | ~r1_xboole_0(B_107, D_108) | ~r1_tarski(C_106, D_108) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.46/12.47  tff(c_469, plain, (![A_110, C_111, C_112, B_113]: (r1_xboole_0(A_110, C_111) | ~r1_tarski(C_111, C_112) | ~r1_tarski(A_110, k4_xboole_0(B_113, C_112)))), inference(resolution, [status(thm)], [c_112, c_450])).
% 21.46/12.47  tff(c_645, plain, (![A_124, B_125]: (r1_xboole_0(A_124, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_124, k4_xboole_0(B_125, '#skF_3')))), inference(resolution, [status(thm)], [c_401, c_469])).
% 21.46/12.47  tff(c_4744, plain, (![A_301, B_302]: (r1_xboole_0(A_301, k1_tops_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_301, '#skF_3') | ~r1_tarski(A_301, B_302))), inference(resolution, [status(thm)], [c_18, c_645])).
% 21.46/12.47  tff(c_4789, plain, (![B_2]: (r1_xboole_0(B_2, k1_tops_1('#skF_1', '#skF_3')) | ~r1_xboole_0(B_2, '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_4744])).
% 21.46/12.47  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.46/12.47  tff(c_30, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 21.46/12.47  tff(c_677, plain, (![A_126, B_127]: (m1_subset_1(k1_tops_1(A_126, B_127), k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.46/12.47  tff(c_20, plain, (![A_18, B_19, C_20]: (k7_subset_1(A_18, B_19, C_20)=k4_xboole_0(B_19, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.46/12.47  tff(c_3630, plain, (![A_255, B_256, C_257]: (k7_subset_1(u1_struct_0(A_255), k1_tops_1(A_255, B_256), C_257)=k4_xboole_0(k1_tops_1(A_255, B_256), C_257) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_677, c_20])).
% 21.46/12.47  tff(c_3637, plain, (![C_257]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_257)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_257) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_3630])).
% 21.46/12.47  tff(c_3644, plain, (![C_257]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_257)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_257))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3637])).
% 21.46/12.47  tff(c_294, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.46/12.47  tff(c_302, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_36, c_294])).
% 21.46/12.47  tff(c_32, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.46/12.47  tff(c_304, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_32])).
% 21.46/12.47  tff(c_3681, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3644, c_304])).
% 21.46/12.47  tff(c_4743, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_3681])).
% 21.46/12.47  tff(c_69750, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4743])).
% 21.46/12.47  tff(c_69753, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_69750])).
% 21.46/12.47  tff(c_69756, plain, (~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_14, c_69753])).
% 21.46/12.47  tff(c_69760, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_69756])).
% 21.46/12.47  tff(c_69763, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_69760])).
% 21.46/12.47  tff(c_69767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_69763])).
% 21.46/12.47  tff(c_69768, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_4743])).
% 21.46/12.47  tff(c_70194, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_4789, c_69768])).
% 21.46/12.47  tff(c_70197, plain, (~l1_pre_topc('#skF_1') | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_438, c_70194])).
% 21.46/12.47  tff(c_70200, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_70197])).
% 21.46/12.47  tff(c_70203, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_70200])).
% 21.46/12.47  tff(c_70207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_70203])).
% 21.46/12.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.46/12.47  
% 21.46/12.47  Inference rules
% 21.46/12.47  ----------------------
% 21.46/12.47  #Ref     : 0
% 21.46/12.47  #Sup     : 18236
% 21.46/12.47  #Fact    : 0
% 21.46/12.47  #Define  : 0
% 21.46/12.47  #Split   : 19
% 21.46/12.47  #Chain   : 0
% 21.46/12.47  #Close   : 0
% 21.46/12.47  
% 21.46/12.47  Ordering : KBO
% 21.46/12.47  
% 21.46/12.47  Simplification rules
% 21.46/12.47  ----------------------
% 21.46/12.47  #Subsume      : 5449
% 21.46/12.47  #Demod        : 8222
% 21.46/12.47  #Tautology    : 6380
% 21.46/12.47  #SimpNegUnit  : 30
% 21.46/12.47  #BackRed      : 4
% 21.46/12.47  
% 21.46/12.47  #Partial instantiations: 0
% 21.46/12.47  #Strategies tried      : 1
% 21.46/12.47  
% 21.46/12.47  Timing (in seconds)
% 21.46/12.47  ----------------------
% 21.46/12.48  Preprocessing        : 0.49
% 21.46/12.48  Parsing              : 0.26
% 21.46/12.48  CNF conversion       : 0.03
% 21.46/12.48  Main loop            : 11.06
% 21.46/12.48  Inferencing          : 1.51
% 21.46/12.48  Reduction            : 5.55
% 21.46/12.48  Demodulation         : 4.82
% 21.46/12.48  BG Simplification    : 0.17
% 21.46/12.48  Subsumption          : 3.33
% 21.46/12.48  Abstraction          : 0.29
% 21.46/12.48  MUC search           : 0.00
% 21.46/12.48  Cooper               : 0.00
% 21.46/12.48  Total                : 11.59
% 21.46/12.48  Index Insertion      : 0.00
% 21.46/12.48  Index Deletion       : 0.00
% 21.46/12.48  Index Matching       : 0.00
% 21.46/12.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
