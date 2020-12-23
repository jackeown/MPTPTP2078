%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:42 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   62 (  96 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 193 expanded)
%              Number of equality atoms :    8 (  15 expanded)
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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_203,plain,(
    ! [A_75,B_76,C_77] :
      ( k7_subset_1(A_75,B_76,C_77) = k4_xboole_0(B_76,C_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_208,plain,(
    ! [C_77] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_77) = k4_xboole_0('#skF_2',C_77) ),
    inference(resolution,[status(thm)],[c_34,c_203])).

tff(c_290,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k7_subset_1(A_88,B_89,C_90),k1_zfmisc_1(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_298,plain,(
    ! [C_77] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_77),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_290])).

tff(c_303,plain,(
    ! [C_77] : m1_subset_1(k4_xboole_0('#skF_2',C_77),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_298])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_tarski(k1_tops_1(A_29,B_33),k1_tops_1(A_29,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_562,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k1_tops_1(A_119,B_120),B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_564,plain,(
    ! [C_77] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_77)),k4_xboole_0('#skF_2',C_77))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_303,c_562])).

tff(c_576,plain,(
    ! [C_77] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_77)),k4_xboole_0('#skF_2',C_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_564])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_573,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_562])).

tff(c_586,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_573])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_xboole_0(A_51,C_52)
      | ~ r1_tarski(A_51,k4_xboole_0(B_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [B_53,C_52] : r1_xboole_0(k4_xboole_0(B_53,C_52),C_52) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_304,plain,(
    ! [A_91,C_92,B_93,D_94] :
      ( r1_xboole_0(A_91,C_92)
      | ~ r1_xboole_0(B_93,D_94)
      | ~ r1_tarski(C_92,D_94)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_313,plain,(
    ! [A_91,C_92,C_52,B_53] :
      ( r1_xboole_0(A_91,C_92)
      | ~ r1_tarski(C_92,C_52)
      | ~ r1_tarski(A_91,k4_xboole_0(B_53,C_52)) ) ),
    inference(resolution,[status(thm)],[c_88,c_304])).

tff(c_680,plain,(
    ! [A_129,B_130] :
      ( r1_xboole_0(A_129,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_129,k4_xboole_0(B_130,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_586,c_313])).

tff(c_705,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_576,c_680])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k4_xboole_0(B_16,C_17))
      | ~ r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_637,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1(k1_tops_1(A_124,B_125),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( k7_subset_1(A_21,B_22,C_23) = k4_xboole_0(B_22,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2247,plain,(
    ! [A_202,B_203,C_204] :
      ( k7_subset_1(u1_struct_0(A_202),k1_tops_1(A_202,B_203),C_204) = k4_xboole_0(k1_tops_1(A_202,B_203),C_204)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(resolution,[status(thm)],[c_637,c_22])).

tff(c_2260,plain,(
    ! [C_204] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_204) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_204)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_2247])).

tff(c_2276,plain,(
    ! [C_204] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_204) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2260])).

tff(c_30,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_210,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_30])).

tff(c_2993,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2276,c_210])).

tff(c_4234,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_2993])).

tff(c_4237,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_4234])).

tff(c_4240,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4237])).

tff(c_4244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_303,c_34,c_12,c_4240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.97  
% 4.92/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.97  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.92/1.97  
% 4.92/1.97  %Foreground sorts:
% 4.92/1.97  
% 4.92/1.97  
% 4.92/1.97  %Background operators:
% 4.92/1.97  
% 4.92/1.97  
% 4.92/1.97  %Foreground operators:
% 4.92/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.92/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.92/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.97  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.92/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.92/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.92/1.97  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.92/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.92/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.92/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.92/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.92/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.97  
% 4.92/1.99  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 4.92/1.99  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.92/1.99  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.92/1.99  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.92/1.99  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 4.92/1.99  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.92/1.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.92/1.99  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.92/1.99  tff(f_53, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 4.92/1.99  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.92/1.99  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.92/1.99  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.92/1.99  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.92/1.99  tff(c_203, plain, (![A_75, B_76, C_77]: (k7_subset_1(A_75, B_76, C_77)=k4_xboole_0(B_76, C_77) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.92/1.99  tff(c_208, plain, (![C_77]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_77)=k4_xboole_0('#skF_2', C_77))), inference(resolution, [status(thm)], [c_34, c_203])).
% 4.92/1.99  tff(c_290, plain, (![A_88, B_89, C_90]: (m1_subset_1(k7_subset_1(A_88, B_89, C_90), k1_zfmisc_1(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.92/1.99  tff(c_298, plain, (![C_77]: (m1_subset_1(k4_xboole_0('#skF_2', C_77), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_208, c_290])).
% 4.92/1.99  tff(c_303, plain, (![C_77]: (m1_subset_1(k4_xboole_0('#skF_2', C_77), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_298])).
% 4.92/1.99  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.92/1.99  tff(c_28, plain, (![A_29, B_33, C_35]: (r1_tarski(k1_tops_1(A_29, B_33), k1_tops_1(A_29, C_35)) | ~r1_tarski(B_33, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.92/1.99  tff(c_562, plain, (![A_119, B_120]: (r1_tarski(k1_tops_1(A_119, B_120), B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.92/1.99  tff(c_564, plain, (![C_77]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_77)), k4_xboole_0('#skF_2', C_77)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_303, c_562])).
% 4.92/1.99  tff(c_576, plain, (![C_77]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_77)), k4_xboole_0('#skF_2', C_77)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_564])).
% 4.92/1.99  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.92/1.99  tff(c_573, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_562])).
% 4.92/1.99  tff(c_586, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_573])).
% 4.92/1.99  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.92/1.99  tff(c_73, plain, (![A_51, C_52, B_53]: (r1_xboole_0(A_51, C_52) | ~r1_tarski(A_51, k4_xboole_0(B_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.92/1.99  tff(c_88, plain, (![B_53, C_52]: (r1_xboole_0(k4_xboole_0(B_53, C_52), C_52))), inference(resolution, [status(thm)], [c_6, c_73])).
% 4.92/1.99  tff(c_304, plain, (![A_91, C_92, B_93, D_94]: (r1_xboole_0(A_91, C_92) | ~r1_xboole_0(B_93, D_94) | ~r1_tarski(C_92, D_94) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.92/1.99  tff(c_313, plain, (![A_91, C_92, C_52, B_53]: (r1_xboole_0(A_91, C_92) | ~r1_tarski(C_92, C_52) | ~r1_tarski(A_91, k4_xboole_0(B_53, C_52)))), inference(resolution, [status(thm)], [c_88, c_304])).
% 4.92/1.99  tff(c_680, plain, (![A_129, B_130]: (r1_xboole_0(A_129, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_129, k4_xboole_0(B_130, '#skF_3')))), inference(resolution, [status(thm)], [c_586, c_313])).
% 4.92/1.99  tff(c_705, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_576, c_680])).
% 4.92/1.99  tff(c_18, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k4_xboole_0(B_16, C_17)) | ~r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.92/1.99  tff(c_637, plain, (![A_124, B_125]: (m1_subset_1(k1_tops_1(A_124, B_125), k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.92/1.99  tff(c_22, plain, (![A_21, B_22, C_23]: (k7_subset_1(A_21, B_22, C_23)=k4_xboole_0(B_22, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.92/1.99  tff(c_2247, plain, (![A_202, B_203, C_204]: (k7_subset_1(u1_struct_0(A_202), k1_tops_1(A_202, B_203), C_204)=k4_xboole_0(k1_tops_1(A_202, B_203), C_204) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(resolution, [status(thm)], [c_637, c_22])).
% 4.92/1.99  tff(c_2260, plain, (![C_204]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_204)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_204) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_2247])).
% 4.92/1.99  tff(c_2276, plain, (![C_204]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_204)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_204))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2260])).
% 4.92/1.99  tff(c_30, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.92/1.99  tff(c_210, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_30])).
% 4.92/1.99  tff(c_2993, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2276, c_210])).
% 4.92/1.99  tff(c_4234, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_2993])).
% 4.92/1.99  tff(c_4237, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_4234])).
% 4.92/1.99  tff(c_4240, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4237])).
% 4.92/1.99  tff(c_4244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_303, c_34, c_12, c_4240])).
% 4.92/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.99  
% 4.92/1.99  Inference rules
% 4.92/1.99  ----------------------
% 4.92/1.99  #Ref     : 0
% 4.92/1.99  #Sup     : 1037
% 4.92/1.99  #Fact    : 0
% 4.92/1.99  #Define  : 0
% 4.92/1.99  #Split   : 7
% 4.92/1.99  #Chain   : 0
% 4.92/1.99  #Close   : 0
% 4.92/1.99  
% 4.92/1.99  Ordering : KBO
% 4.92/1.99  
% 4.92/1.99  Simplification rules
% 4.92/1.99  ----------------------
% 4.92/1.99  #Subsume      : 119
% 4.92/1.99  #Demod        : 518
% 4.92/1.99  #Tautology    : 453
% 4.92/1.99  #SimpNegUnit  : 0
% 4.92/1.99  #BackRed      : 2
% 4.92/1.99  
% 4.92/1.99  #Partial instantiations: 0
% 4.92/1.99  #Strategies tried      : 1
% 4.92/1.99  
% 4.92/1.99  Timing (in seconds)
% 4.92/1.99  ----------------------
% 4.92/1.99  Preprocessing        : 0.32
% 4.92/1.99  Parsing              : 0.18
% 4.92/1.99  CNF conversion       : 0.02
% 4.92/1.99  Main loop            : 0.87
% 4.92/1.99  Inferencing          : 0.26
% 4.92/1.99  Reduction            : 0.34
% 4.92/1.99  Demodulation         : 0.27
% 4.92/1.99  BG Simplification    : 0.03
% 4.92/1.99  Subsumption          : 0.18
% 4.92/1.99  Abstraction          : 0.04
% 4.92/1.99  MUC search           : 0.00
% 4.92/1.99  Cooper               : 0.00
% 4.92/1.99  Total                : 1.22
% 4.92/1.99  Index Insertion      : 0.00
% 4.92/1.99  Index Deletion       : 0.00
% 4.92/1.99  Index Matching       : 0.00
% 4.92/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
