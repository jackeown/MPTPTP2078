%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:54 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 152 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 323 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_20,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_29,B_30,C_31] :
      ( k4_subset_1(A_29,B_30,C_31) = k2_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [B_32] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_32,'#skF_2') = k2_xboole_0(B_32,'#skF_2')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_87,plain,(
    ! [B_18] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_18),'#skF_2') = k2_xboole_0(k2_tops_1('#skF_1',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_83])).

tff(c_121,plain,(
    ! [B_37] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_37),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_37))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_87])).

tff(c_132,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_121])).

tff(c_138,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k3_subset_1(A_41,k4_subset_1(A_41,B_42,C_43)),k3_subset_1(A_41,B_42))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_138])).

tff(c_149,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_154,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_157,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_157])).

tff(c_163,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_22,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( k2_pre_topc(A_27,B_28) = B_28
      | ~ v4_pre_topc(B_28,A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_67,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_71,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_67])).

tff(c_108,plain,(
    ! [A_35,B_36] :
      ( k4_subset_1(u1_struct_0(A_35),B_36,k2_tops_1(A_35,B_36)) = k2_pre_topc(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_112,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_108])).

tff(c_116,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_71,c_112])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( k4_subset_1(A_3,B_4,C_5) = k2_xboole_0(B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_244,plain,(
    ! [B_47] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_47,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_47,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_254,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_244])).

tff(c_260,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_254])).

tff(c_162,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_262,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_162])).

tff(c_6,plain,(
    ! [B_7,C_9,A_6] :
      ( r1_tarski(B_7,C_9)
      | ~ r1_tarski(k3_subset_1(A_6,C_9),k3_subset_1(A_6,B_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_279,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_262,c_6])).

tff(c_282,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_24,c_279])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:07:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.74  
% 2.63/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.75  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.63/1.75  
% 2.63/1.75  %Foreground sorts:
% 2.63/1.75  
% 2.63/1.75  
% 2.63/1.75  %Background operators:
% 2.63/1.75  
% 2.63/1.75  
% 2.63/1.75  %Foreground operators:
% 2.63/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.75  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.63/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.75  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.63/1.75  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.75  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.75  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.63/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.75  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.63/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.75  
% 2.63/1.77  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.63/1.77  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.63/1.77  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.63/1.77  tff(f_33, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.63/1.77  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 2.63/1.77  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.63/1.77  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.63/1.77  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.63/1.77  tff(c_20, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.77  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.77  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.77  tff(c_16, plain, (![A_17, B_18]: (m1_subset_1(k2_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.77  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.77  tff(c_76, plain, (![A_29, B_30, C_31]: (k4_subset_1(A_29, B_30, C_31)=k2_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.77  tff(c_83, plain, (![B_32]: (k4_subset_1(u1_struct_0('#skF_1'), B_32, '#skF_2')=k2_xboole_0(B_32, '#skF_2') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_24, c_76])).
% 2.63/1.77  tff(c_87, plain, (![B_18]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_18), '#skF_2')=k2_xboole_0(k2_tops_1('#skF_1', B_18), '#skF_2') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_83])).
% 2.63/1.77  tff(c_121, plain, (![B_37]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_37), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_37)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_87])).
% 2.63/1.77  tff(c_132, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_121])).
% 2.63/1.77  tff(c_138, plain, (![A_41, B_42, C_43]: (r1_tarski(k3_subset_1(A_41, k4_subset_1(A_41, B_42, C_43)), k3_subset_1(A_41, B_42)) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.77  tff(c_141, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_138])).
% 2.63/1.77  tff(c_149, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_141])).
% 2.63/1.77  tff(c_154, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_149])).
% 2.63/1.77  tff(c_157, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_154])).
% 2.63/1.77  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_157])).
% 2.63/1.77  tff(c_163, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_149])).
% 2.63/1.77  tff(c_22, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.77  tff(c_61, plain, (![A_27, B_28]: (k2_pre_topc(A_27, B_28)=B_28 | ~v4_pre_topc(B_28, A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.63/1.77  tff(c_67, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.63/1.77  tff(c_71, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_67])).
% 2.63/1.77  tff(c_108, plain, (![A_35, B_36]: (k4_subset_1(u1_struct_0(A_35), B_36, k2_tops_1(A_35, B_36))=k2_pre_topc(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.63/1.77  tff(c_112, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_108])).
% 2.63/1.77  tff(c_116, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_71, c_112])).
% 2.63/1.77  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_subset_1(A_3, B_4, C_5)=k2_xboole_0(B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.77  tff(c_244, plain, (![B_47]: (k4_subset_1(u1_struct_0('#skF_1'), B_47, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_47, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_163, c_4])).
% 2.63/1.77  tff(c_254, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_244])).
% 2.63/1.77  tff(c_260, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_254])).
% 2.63/1.77  tff(c_162, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_149])).
% 2.63/1.77  tff(c_262, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_162])).
% 2.63/1.77  tff(c_6, plain, (![B_7, C_9, A_6]: (r1_tarski(B_7, C_9) | ~r1_tarski(k3_subset_1(A_6, C_9), k3_subset_1(A_6, B_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.77  tff(c_279, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_262, c_6])).
% 2.63/1.77  tff(c_282, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_24, c_279])).
% 2.63/1.77  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_282])).
% 2.63/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.77  
% 2.63/1.77  Inference rules
% 2.63/1.77  ----------------------
% 2.63/1.77  #Ref     : 0
% 2.63/1.77  #Sup     : 58
% 2.63/1.77  #Fact    : 0
% 2.63/1.77  #Define  : 0
% 2.63/1.77  #Split   : 4
% 2.63/1.77  #Chain   : 0
% 2.63/1.77  #Close   : 0
% 2.63/1.77  
% 2.63/1.77  Ordering : KBO
% 2.63/1.77  
% 2.63/1.77  Simplification rules
% 2.63/1.77  ----------------------
% 2.63/1.77  #Subsume      : 2
% 2.63/1.77  #Demod        : 35
% 2.63/1.77  #Tautology    : 25
% 2.63/1.77  #SimpNegUnit  : 2
% 2.63/1.77  #BackRed      : 2
% 2.63/1.77  
% 2.63/1.77  #Partial instantiations: 0
% 2.63/1.77  #Strategies tried      : 1
% 2.63/1.77  
% 2.63/1.77  Timing (in seconds)
% 2.63/1.77  ----------------------
% 2.63/1.77  Preprocessing        : 0.51
% 2.63/1.77  Parsing              : 0.27
% 2.63/1.77  CNF conversion       : 0.03
% 2.63/1.77  Main loop            : 0.34
% 2.63/1.77  Inferencing          : 0.12
% 2.63/1.77  Reduction            : 0.11
% 2.63/1.77  Demodulation         : 0.09
% 2.63/1.78  BG Simplification    : 0.02
% 2.63/1.78  Subsumption          : 0.06
% 2.63/1.78  Abstraction          : 0.02
% 2.63/1.78  MUC search           : 0.00
% 2.63/1.78  Cooper               : 0.00
% 2.63/1.78  Total                : 0.91
% 2.63/1.78  Index Insertion      : 0.00
% 2.63/1.78  Index Deletion       : 0.00
% 2.63/1.78  Index Matching       : 0.00
% 2.63/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
