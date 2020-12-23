%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:23 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 286 expanded)
%              Number of leaves         :   25 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 499 expanded)
%              Number of equality atoms :   29 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k2_struct_0(A)
                & k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) != k1_xboole_0
                & B = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_21] :
      ( u1_struct_0(A_21) = k2_struct_0(A_21)
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_48,plain,(
    ! [A_27] :
      ( m1_subset_1(k2_struct_0(A_27),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_48])).

tff(c_52,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_55,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_52])).

tff(c_59,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_55])).

tff(c_60,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_103,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k2_pre_topc(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_110,plain,(
    ! [B_36] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_36),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_103])).

tff(c_114,plain,(
    ! [B_36] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_36),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_37,c_110])).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_61,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_12,plain,(
    ! [A_9] :
      ( m1_subset_1(k2_struct_0(A_9),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_167,plain,(
    ! [A_43] :
      ( k7_subset_1(u1_struct_0(A_43),k2_struct_0(A_43),k2_struct_0(A_43)) = k1_xboole_0
      | ~ m1_subset_1(k2_struct_0(A_43),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_179,plain,(
    ! [A_44] :
      ( k7_subset_1(u1_struct_0(A_44),k2_struct_0(A_44),k2_struct_0(A_44)) = k1_xboole_0
      | ~ l1_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_12,c_167])).

tff(c_67,plain,(
    ! [A_28,B_29,C_30] :
      ( k7_subset_1(A_28,B_29,C_30) = k4_xboole_0(B_29,C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_9,C_30] :
      ( k7_subset_1(u1_struct_0(A_9),k2_struct_0(A_9),C_30) = k4_xboole_0(k2_struct_0(A_9),C_30)
      | ~ l1_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_185,plain,(
    ! [A_44] :
      ( k4_xboole_0(k2_struct_0(A_44),k2_struct_0(A_44)) = k1_xboole_0
      | ~ l1_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_73])).

tff(c_72,plain,(
    ! [C_30] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_30) = k4_xboole_0(k2_struct_0('#skF_1'),C_30) ),
    inference(resolution,[status(thm)],[c_60,c_67])).

tff(c_262,plain,(
    ! [A_54,B_55] :
      ( k7_subset_1(u1_struct_0(A_54),k2_struct_0(A_54),k7_subset_1(u1_struct_0(A_54),k2_struct_0(A_54),B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_292,plain,(
    ! [B_55] :
      ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_262])).

tff(c_316,plain,(
    ! [B_57] :
      ( k4_xboole_0(k2_struct_0('#skF_1'),k4_xboole_0(k2_struct_0('#skF_1'),B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_37,c_72,c_72,c_37,c_292])).

tff(c_332,plain,
    ( k4_xboole_0(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_316])).

tff(c_348,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_61,c_60,c_332])).

tff(c_83,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(B_32,k2_pre_topc(A_33,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,(
    ! [A_37] :
      ( r1_tarski(k2_struct_0(A_37),k2_pre_topc(A_37,k2_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_12,c_83])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    ! [A_37] :
      ( k4_xboole_0(k2_struct_0(A_37),k2_pre_topc(A_37,k2_struct_0(A_37))) = k1_xboole_0
      | ~ l1_pre_topc(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_339,plain,
    ( k4_xboole_0(k2_struct_0('#skF_1'),k1_xboole_0) = k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_316])).

tff(c_352,plain,
    ( k4_xboole_0(k2_struct_0('#skF_1'),k1_xboole_0) = k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_26,c_339])).

tff(c_362,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_352])).

tff(c_363,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_362])).

tff(c_366,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_114,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:14:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.26  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.18/1.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.18/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.26  
% 2.18/1.27  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.18/1.27  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.18/1.27  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.18/1.27  tff(f_47, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.18/1.27  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.18/1.27  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k2_struct_0(A)) & (k7_subset_1(u1_struct_0(A), k2_struct_0(A), B) = k1_xboole_0)) & ~(~(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B) = k1_xboole_0) & (B = k2_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 2.18/1.27  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.18/1.27  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 2.18/1.27  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.18/1.27  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.18/1.27  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.27  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.27  tff(c_28, plain, (![A_21]: (u1_struct_0(A_21)=k2_struct_0(A_21) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.27  tff(c_33, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_14, c_28])).
% 2.18/1.27  tff(c_37, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_33])).
% 2.18/1.27  tff(c_48, plain, (![A_27]: (m1_subset_1(k2_struct_0(A_27), k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.27  tff(c_51, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_48])).
% 2.18/1.27  tff(c_52, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_51])).
% 2.18/1.27  tff(c_55, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_52])).
% 2.18/1.27  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_55])).
% 2.18/1.27  tff(c_60, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_51])).
% 2.18/1.27  tff(c_103, plain, (![A_35, B_36]: (m1_subset_1(k2_pre_topc(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.27  tff(c_110, plain, (![B_36]: (m1_subset_1(k2_pre_topc('#skF_1', B_36), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_103])).
% 2.18/1.27  tff(c_114, plain, (![B_36]: (m1_subset_1(k2_pre_topc('#skF_1', B_36), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_37, c_110])).
% 2.18/1.27  tff(c_24, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.27  tff(c_61, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_51])).
% 2.18/1.27  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_struct_0(A_9), k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.27  tff(c_167, plain, (![A_43]: (k7_subset_1(u1_struct_0(A_43), k2_struct_0(A_43), k2_struct_0(A_43))=k1_xboole_0 | ~m1_subset_1(k2_struct_0(A_43), k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.27  tff(c_179, plain, (![A_44]: (k7_subset_1(u1_struct_0(A_44), k2_struct_0(A_44), k2_struct_0(A_44))=k1_xboole_0 | ~l1_struct_0(A_44))), inference(resolution, [status(thm)], [c_12, c_167])).
% 2.18/1.27  tff(c_67, plain, (![A_28, B_29, C_30]: (k7_subset_1(A_28, B_29, C_30)=k4_xboole_0(B_29, C_30) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.27  tff(c_73, plain, (![A_9, C_30]: (k7_subset_1(u1_struct_0(A_9), k2_struct_0(A_9), C_30)=k4_xboole_0(k2_struct_0(A_9), C_30) | ~l1_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_67])).
% 2.18/1.27  tff(c_185, plain, (![A_44]: (k4_xboole_0(k2_struct_0(A_44), k2_struct_0(A_44))=k1_xboole_0 | ~l1_struct_0(A_44) | ~l1_struct_0(A_44))), inference(superposition, [status(thm), theory('equality')], [c_179, c_73])).
% 2.18/1.27  tff(c_72, plain, (![C_30]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_30)=k4_xboole_0(k2_struct_0('#skF_1'), C_30))), inference(resolution, [status(thm)], [c_60, c_67])).
% 2.18/1.27  tff(c_262, plain, (![A_54, B_55]: (k7_subset_1(u1_struct_0(A_54), k2_struct_0(A_54), k7_subset_1(u1_struct_0(A_54), k2_struct_0(A_54), B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.27  tff(c_292, plain, (![B_55]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_262])).
% 2.18/1.27  tff(c_316, plain, (![B_57]: (k4_xboole_0(k2_struct_0('#skF_1'), k4_xboole_0(k2_struct_0('#skF_1'), B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_37, c_72, c_72, c_37, c_292])).
% 2.18/1.27  tff(c_332, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_185, c_316])).
% 2.18/1.27  tff(c_348, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_61, c_60, c_332])).
% 2.18/1.27  tff(c_83, plain, (![B_32, A_33]: (r1_tarski(B_32, k2_pre_topc(A_33, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.27  tff(c_115, plain, (![A_37]: (r1_tarski(k2_struct_0(A_37), k2_pre_topc(A_37, k2_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~l1_struct_0(A_37))), inference(resolution, [status(thm)], [c_12, c_83])).
% 2.18/1.27  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.27  tff(c_119, plain, (![A_37]: (k4_xboole_0(k2_struct_0(A_37), k2_pre_topc(A_37, k2_struct_0(A_37)))=k1_xboole_0 | ~l1_pre_topc(A_37) | ~l1_struct_0(A_37))), inference(resolution, [status(thm)], [c_115, c_4])).
% 2.18/1.27  tff(c_339, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_xboole_0)=k2_pre_topc('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_119, c_316])).
% 2.18/1.27  tff(c_352, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_xboole_0)=k2_pre_topc('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_26, c_339])).
% 2.18/1.27  tff(c_362, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_352])).
% 2.18/1.27  tff(c_363, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_24, c_362])).
% 2.18/1.27  tff(c_366, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_114, c_363])).
% 2.18/1.27  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_366])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 80
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 1
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.28  #Subsume      : 3
% 2.18/1.28  #Demod        : 46
% 2.18/1.28  #Tautology    : 42
% 2.18/1.28  #SimpNegUnit  : 1
% 2.18/1.28  #BackRed      : 0
% 2.18/1.28  
% 2.18/1.28  #Partial instantiations: 0
% 2.18/1.28  #Strategies tried      : 1
% 2.18/1.28  
% 2.18/1.28  Timing (in seconds)
% 2.18/1.28  ----------------------
% 2.18/1.28  Preprocessing        : 0.30
% 2.18/1.28  Parsing              : 0.17
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.22
% 2.18/1.28  Inferencing          : 0.09
% 2.18/1.28  Reduction            : 0.06
% 2.18/1.28  Demodulation         : 0.04
% 2.18/1.28  BG Simplification    : 0.01
% 2.18/1.28  Subsumption          : 0.04
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.56
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
