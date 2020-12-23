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
% DateTime   : Thu Dec  3 10:22:54 EST 2020

% Result     : Theorem 21.64s
% Output     : CNFRefutation 21.64s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 127 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_76,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_85,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    k2_xboole_0('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) = k1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_85])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_126,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_547,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(k4_xboole_0(A_71,B_72),C_73)
      | ~ r1_tarski(A_71,k2_xboole_0(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_291,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_558,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_tarski(A_71,k2_xboole_0(B_72,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_547,c_291])).

tff(c_579,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_558])).

tff(c_868,plain,(
    ! [A_81,B_82] : k4_xboole_0(k4_xboole_0(A_81,B_82),A_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_579])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,k2_xboole_0(B_17,C_18))
      | ~ r1_tarski(k4_xboole_0(A_16,B_17),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_886,plain,(
    ! [A_81,B_82,C_18] :
      ( r1_tarski(k4_xboole_0(A_81,B_82),k2_xboole_0(A_81,C_18))
      | ~ r1_tarski(k1_xboole_0,C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_20])).

tff(c_1248,plain,(
    ! [A_91,B_92,C_93] : r1_tarski(k4_xboole_0(A_91,B_92),k2_xboole_0(A_91,C_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_886])).

tff(c_1298,plain,(
    ! [B_92] : r1_tarski(k4_xboole_0('#skF_2',B_92),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1248])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1782,plain,(
    ! [B_113,A_114,C_115] :
      ( v2_tops_2(B_113,A_114)
      | ~ v2_tops_2(C_115,A_114)
      | ~ r1_tarski(B_113,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_114))))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_114))))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8892,plain,(
    ! [A_211,B_212,A_213] :
      ( v2_tops_2(k4_xboole_0(A_211,B_212),A_213)
      | ~ v2_tops_2(A_211,A_213)
      | ~ m1_subset_1(A_211,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_213))))
      | ~ m1_subset_1(k4_xboole_0(A_211,B_212),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_213))))
      | ~ l1_pre_topc(A_213) ) ),
    inference(resolution,[status(thm)],[c_14,c_1782])).

tff(c_81166,plain,(
    ! [A_754,B_755,A_756] :
      ( v2_tops_2(k4_xboole_0(A_754,B_755),A_756)
      | ~ v2_tops_2(A_754,A_756)
      | ~ m1_subset_1(A_754,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_756))))
      | ~ l1_pre_topc(A_756)
      | ~ r1_tarski(k4_xboole_0(A_754,B_755),k1_zfmisc_1(u1_struct_0(A_756))) ) ),
    inference(resolution,[status(thm)],[c_26,c_8892])).

tff(c_81382,plain,(
    ! [B_92] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_92),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1298,c_81166])).

tff(c_81524,plain,(
    ! [B_92] : v2_tops_2(k4_xboole_0('#skF_2',B_92),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_81382])).

tff(c_1482,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1491,plain,(
    ! [C_102] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_102) = k4_xboole_0('#skF_2',C_102) ),
    inference(resolution,[status(thm)],[c_36,c_1482])).

tff(c_30,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1846,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_30])).

tff(c_81548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81524,c_1846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.64/13.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.64/13.87  
% 21.64/13.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.64/13.87  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 21.64/13.87  
% 21.64/13.87  %Foreground sorts:
% 21.64/13.87  
% 21.64/13.87  
% 21.64/13.87  %Background operators:
% 21.64/13.87  
% 21.64/13.87  
% 21.64/13.87  %Foreground operators:
% 21.64/13.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.64/13.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.64/13.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.64/13.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.64/13.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.64/13.87  tff('#skF_2', type, '#skF_2': $i).
% 21.64/13.87  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 21.64/13.87  tff('#skF_3', type, '#skF_3': $i).
% 21.64/13.87  tff('#skF_1', type, '#skF_1': $i).
% 21.64/13.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.64/13.87  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 21.64/13.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.64/13.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.64/13.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.64/13.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.64/13.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.64/13.87  
% 21.64/13.88  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tops_2)).
% 21.64/13.88  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.64/13.88  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 21.64/13.88  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 21.64/13.88  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.64/13.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 21.64/13.88  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 21.64/13.88  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.64/13.88  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 21.64/13.88  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 21.64/13.88  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 21.64/13.88  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 21.64/13.88  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 21.64/13.88  tff(c_32, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 21.64/13.88  tff(c_76, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.64/13.88  tff(c_84, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_76])).
% 21.64/13.88  tff(c_85, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.64/13.88  tff(c_101, plain, (k2_xboole_0('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))=k1_zfmisc_1(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_85])).
% 21.64/13.88  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.64/13.88  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.64/13.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.64/13.88  tff(c_106, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(resolution, [status(thm)], [c_12, c_85])).
% 21.64/13.88  tff(c_126, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 21.64/13.88  tff(c_547, plain, (![A_71, B_72, C_73]: (r1_tarski(k4_xboole_0(A_71, B_72), C_73) | ~r1_tarski(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.64/13.88  tff(c_277, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.64/13.88  tff(c_291, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_277])).
% 21.64/13.88  tff(c_558, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_tarski(A_71, k2_xboole_0(B_72, k1_xboole_0)))), inference(resolution, [status(thm)], [c_547, c_291])).
% 21.64/13.88  tff(c_579, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_tarski(A_74, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_558])).
% 21.64/13.88  tff(c_868, plain, (![A_81, B_82]: (k4_xboole_0(k4_xboole_0(A_81, B_82), A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_579])).
% 21.64/13.88  tff(c_20, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, k2_xboole_0(B_17, C_18)) | ~r1_tarski(k4_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.64/13.88  tff(c_886, plain, (![A_81, B_82, C_18]: (r1_tarski(k4_xboole_0(A_81, B_82), k2_xboole_0(A_81, C_18)) | ~r1_tarski(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_868, c_20])).
% 21.64/13.88  tff(c_1248, plain, (![A_91, B_92, C_93]: (r1_tarski(k4_xboole_0(A_91, B_92), k2_xboole_0(A_91, C_93)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_886])).
% 21.64/13.88  tff(c_1298, plain, (![B_92]: (r1_tarski(k4_xboole_0('#skF_2', B_92), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1248])).
% 21.64/13.88  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.64/13.88  tff(c_1782, plain, (![B_113, A_114, C_115]: (v2_tops_2(B_113, A_114) | ~v2_tops_2(C_115, A_114) | ~r1_tarski(B_113, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_114)))) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_114)))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.64/13.88  tff(c_8892, plain, (![A_211, B_212, A_213]: (v2_tops_2(k4_xboole_0(A_211, B_212), A_213) | ~v2_tops_2(A_211, A_213) | ~m1_subset_1(A_211, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_213)))) | ~m1_subset_1(k4_xboole_0(A_211, B_212), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_213)))) | ~l1_pre_topc(A_213))), inference(resolution, [status(thm)], [c_14, c_1782])).
% 21.64/13.88  tff(c_81166, plain, (![A_754, B_755, A_756]: (v2_tops_2(k4_xboole_0(A_754, B_755), A_756) | ~v2_tops_2(A_754, A_756) | ~m1_subset_1(A_754, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_756)))) | ~l1_pre_topc(A_756) | ~r1_tarski(k4_xboole_0(A_754, B_755), k1_zfmisc_1(u1_struct_0(A_756))))), inference(resolution, [status(thm)], [c_26, c_8892])).
% 21.64/13.88  tff(c_81382, plain, (![B_92]: (v2_tops_2(k4_xboole_0('#skF_2', B_92), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1298, c_81166])).
% 21.64/13.88  tff(c_81524, plain, (![B_92]: (v2_tops_2(k4_xboole_0('#skF_2', B_92), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_81382])).
% 21.64/13.88  tff(c_1482, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.64/13.88  tff(c_1491, plain, (![C_102]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_102)=k4_xboole_0('#skF_2', C_102))), inference(resolution, [status(thm)], [c_36, c_1482])).
% 21.64/13.88  tff(c_30, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 21.64/13.88  tff(c_1846, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1491, c_30])).
% 21.64/13.88  tff(c_81548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81524, c_1846])).
% 21.64/13.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.64/13.88  
% 21.64/13.88  Inference rules
% 21.64/13.88  ----------------------
% 21.64/13.88  #Ref     : 0
% 21.64/13.88  #Sup     : 19394
% 21.64/13.88  #Fact    : 0
% 21.64/13.88  #Define  : 0
% 21.64/13.88  #Split   : 4
% 21.64/13.88  #Chain   : 0
% 21.64/13.88  #Close   : 0
% 21.64/13.88  
% 21.64/13.88  Ordering : KBO
% 21.64/13.88  
% 21.64/13.88  Simplification rules
% 21.64/13.88  ----------------------
% 21.64/13.88  #Subsume      : 1029
% 21.64/13.88  #Demod        : 20089
% 21.64/13.88  #Tautology    : 10294
% 21.64/13.88  #SimpNegUnit  : 4
% 21.64/13.88  #BackRed      : 19
% 21.64/13.88  
% 21.64/13.88  #Partial instantiations: 0
% 21.64/13.89  #Strategies tried      : 1
% 21.64/13.89  
% 21.64/13.89  Timing (in seconds)
% 21.64/13.89  ----------------------
% 21.64/13.89  Preprocessing        : 0.32
% 21.64/13.89  Parsing              : 0.17
% 21.64/13.89  CNF conversion       : 0.02
% 21.64/13.89  Main loop            : 12.80
% 21.64/13.89  Inferencing          : 1.34
% 21.64/13.89  Reduction            : 8.09
% 21.64/13.89  Demodulation         : 7.49
% 21.64/13.89  BG Simplification    : 0.20
% 21.64/13.89  Subsumption          : 2.67
% 21.64/13.89  Abstraction          : 0.32
% 21.64/13.89  MUC search           : 0.00
% 21.64/13.89  Cooper               : 0.00
% 21.64/13.89  Total                : 13.16
% 21.64/13.89  Index Insertion      : 0.00
% 21.64/13.89  Index Deletion       : 0.00
% 21.64/13.89  Index Matching       : 0.00
% 21.64/13.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
