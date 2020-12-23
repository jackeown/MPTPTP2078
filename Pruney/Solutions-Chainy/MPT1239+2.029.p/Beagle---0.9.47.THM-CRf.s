%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:44 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 121 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 248 expanded)
%              Number of equality atoms :    8 (  22 expanded)
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

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_140,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tops_1(A_86,B_87),B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_151,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_164,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_151])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_49,plain,(
    ! [A_52,B_53,C_54] :
      ( k7_subset_1(A_52,B_53,C_54) = k4_xboole_0(B_53,C_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    ! [C_55] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_55) = k4_xboole_0('#skF_2',C_55) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [C_55] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_55),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_72,plain,(
    ! [C_55] : m1_subset_1(k4_xboole_0('#skF_2',C_55),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_144,plain,(
    ! [C_55] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_55)),k4_xboole_0('#skF_2',C_55))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_72,c_140])).

tff(c_178,plain,(
    ! [C_90] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_90)),k4_xboole_0('#skF_2',C_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_144])).

tff(c_33,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_xboole_0(A_40,k4_xboole_0(C_41,B_42))
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [C_41,B_42,A_40] :
      ( r1_xboole_0(k4_xboole_0(C_41,B_42),A_40)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_41,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,C_47)
      | ~ r1_xboole_0(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_46,A_40,C_41,B_42] :
      ( r1_xboole_0(A_46,A_40)
      | ~ r1_tarski(A_46,k4_xboole_0(C_41,B_42))
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(resolution,[status(thm)],[c_36,c_41])).

tff(c_183,plain,(
    ! [C_90,A_40] :
      ( r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_90)),A_40)
      | ~ r1_tarski(A_40,C_90) ) ),
    inference(resolution,[status(thm)],[c_178,c_46])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_25,B_29,C_31] :
      ( r1_tarski(k1_tops_1(A_25,B_29),k1_tops_1(A_25,C_31))
      | ~ r1_tarski(B_29,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(A_11,k4_xboole_0(B_12,C_13))
      | ~ r1_xboole_0(A_11,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k1_tops_1(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_491,plain,(
    ! [A_155,B_156,C_157] :
      ( k7_subset_1(u1_struct_0(A_155),k1_tops_1(A_155,B_156),C_157) = k4_xboole_0(k1_tops_1(A_155,B_156),C_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_165,c_14])).

tff(c_506,plain,(
    ! [C_157] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_157) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_157)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_491])).

tff(c_525,plain,(
    ! [C_157] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_157) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_506])).

tff(c_57,plain,(
    ! [C_54] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_54) = k4_xboole_0('#skF_2',C_54) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_22,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_59,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_22])).

tff(c_529,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_59])).

tff(c_564,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_529])).

tff(c_912,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_915,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_912])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_72,c_26,c_4,c_915])).

tff(c_920,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_924,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_920])).

tff(c_928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:04:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.52  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.52  
% 3.21/1.52  %Foreground sorts:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Background operators:
% 3.21/1.52  
% 3.21/1.52  
% 3.21/1.52  %Foreground operators:
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.21/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.21/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.52  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.21/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.52  
% 3.55/1.53  tff(f_93, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 3.55/1.53  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.55/1.53  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.55/1.53  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.55/1.53  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.55/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.55/1.53  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.55/1.53  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.55/1.53  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.55/1.53  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.55/1.53  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.55/1.53  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.53  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.53  tff(c_140, plain, (![A_86, B_87]: (r1_tarski(k1_tops_1(A_86, B_87), B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.53  tff(c_151, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_140])).
% 3.55/1.53  tff(c_164, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_151])).
% 3.55/1.53  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.53  tff(c_49, plain, (![A_52, B_53, C_54]: (k7_subset_1(A_52, B_53, C_54)=k4_xboole_0(B_53, C_54) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.53  tff(c_60, plain, (![C_55]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_55)=k4_xboole_0('#skF_2', C_55))), inference(resolution, [status(thm)], [c_26, c_49])).
% 3.55/1.53  tff(c_12, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.53  tff(c_66, plain, (![C_55]: (m1_subset_1(k4_xboole_0('#skF_2', C_55), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 3.55/1.53  tff(c_72, plain, (![C_55]: (m1_subset_1(k4_xboole_0('#skF_2', C_55), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 3.55/1.53  tff(c_144, plain, (![C_55]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_55)), k4_xboole_0('#skF_2', C_55)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_140])).
% 3.55/1.53  tff(c_178, plain, (![C_90]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_90)), k4_xboole_0('#skF_2', C_90)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_144])).
% 3.55/1.53  tff(c_33, plain, (![A_40, C_41, B_42]: (r1_xboole_0(A_40, k4_xboole_0(C_41, B_42)) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.55/1.53  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.53  tff(c_36, plain, (![C_41, B_42, A_40]: (r1_xboole_0(k4_xboole_0(C_41, B_42), A_40) | ~r1_tarski(A_40, B_42))), inference(resolution, [status(thm)], [c_33, c_2])).
% 3.55/1.53  tff(c_41, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, C_47) | ~r1_xboole_0(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.53  tff(c_46, plain, (![A_46, A_40, C_41, B_42]: (r1_xboole_0(A_46, A_40) | ~r1_tarski(A_46, k4_xboole_0(C_41, B_42)) | ~r1_tarski(A_40, B_42))), inference(resolution, [status(thm)], [c_36, c_41])).
% 3.55/1.53  tff(c_183, plain, (![C_90, A_40]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_90)), A_40) | ~r1_tarski(A_40, C_90))), inference(resolution, [status(thm)], [c_178, c_46])).
% 3.55/1.53  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.53  tff(c_20, plain, (![A_25, B_29, C_31]: (r1_tarski(k1_tops_1(A_25, B_29), k1_tops_1(A_25, C_31)) | ~r1_tarski(B_29, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.53  tff(c_10, plain, (![A_11, B_12, C_13]: (r1_tarski(A_11, k4_xboole_0(B_12, C_13)) | ~r1_xboole_0(A_11, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.53  tff(c_165, plain, (![A_88, B_89]: (m1_subset_1(k1_tops_1(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.55/1.53  tff(c_14, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.53  tff(c_491, plain, (![A_155, B_156, C_157]: (k7_subset_1(u1_struct_0(A_155), k1_tops_1(A_155, B_156), C_157)=k4_xboole_0(k1_tops_1(A_155, B_156), C_157) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(resolution, [status(thm)], [c_165, c_14])).
% 3.55/1.53  tff(c_506, plain, (![C_157]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_157)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_157) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_491])).
% 3.55/1.53  tff(c_525, plain, (![C_157]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_157)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_157))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_506])).
% 3.55/1.53  tff(c_57, plain, (![C_54]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_54)=k4_xboole_0('#skF_2', C_54))), inference(resolution, [status(thm)], [c_26, c_49])).
% 3.55/1.53  tff(c_22, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.55/1.53  tff(c_59, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_22])).
% 3.55/1.53  tff(c_529, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_59])).
% 3.55/1.53  tff(c_564, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_529])).
% 3.55/1.53  tff(c_912, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_564])).
% 3.55/1.53  tff(c_915, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_912])).
% 3.55/1.53  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_72, c_26, c_4, c_915])).
% 3.55/1.53  tff(c_920, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_564])).
% 3.55/1.53  tff(c_924, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_183, c_920])).
% 3.55/1.53  tff(c_928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_924])).
% 3.55/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.53  
% 3.55/1.53  Inference rules
% 3.55/1.53  ----------------------
% 3.55/1.53  #Ref     : 0
% 3.55/1.53  #Sup     : 231
% 3.55/1.53  #Fact    : 0
% 3.55/1.53  #Define  : 0
% 3.55/1.53  #Split   : 7
% 3.55/1.53  #Chain   : 0
% 3.55/1.53  #Close   : 0
% 3.55/1.53  
% 3.55/1.53  Ordering : KBO
% 3.55/1.53  
% 3.55/1.53  Simplification rules
% 3.55/1.53  ----------------------
% 3.55/1.53  #Subsume      : 23
% 3.55/1.53  #Demod        : 87
% 3.55/1.53  #Tautology    : 20
% 3.55/1.53  #SimpNegUnit  : 0
% 3.55/1.53  #BackRed      : 2
% 3.55/1.53  
% 3.55/1.53  #Partial instantiations: 0
% 3.55/1.53  #Strategies tried      : 1
% 3.55/1.53  
% 3.55/1.53  Timing (in seconds)
% 3.55/1.53  ----------------------
% 3.55/1.53  Preprocessing        : 0.30
% 3.55/1.53  Parsing              : 0.17
% 3.55/1.53  CNF conversion       : 0.02
% 3.55/1.53  Main loop            : 0.47
% 3.55/1.53  Inferencing          : 0.17
% 3.55/1.53  Reduction            : 0.13
% 3.55/1.53  Demodulation         : 0.09
% 3.55/1.53  BG Simplification    : 0.02
% 3.55/1.53  Subsumption          : 0.11
% 3.55/1.53  Abstraction          : 0.02
% 3.55/1.53  MUC search           : 0.00
% 3.55/1.53  Cooper               : 0.00
% 3.55/1.53  Total                : 0.80
% 3.55/1.54  Index Insertion      : 0.00
% 3.55/1.54  Index Deletion       : 0.00
% 3.55/1.54  Index Matching       : 0.00
% 3.55/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
