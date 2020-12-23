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
% DateTime   : Thu Dec  3 10:20:23 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 120 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   76 ( 178 expanded)
%              Number of equality atoms :   21 (  56 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(c_8,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_195,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_pre_topc(A_39,B_40),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_203,plain,(
    ! [B_40] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_40),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_195])).

tff(c_207,plain,(
    ! [B_40] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_40),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56,c_203])).

tff(c_26,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(B_35,k2_pre_topc(A_36,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_152,plain,(
    ! [A_37] :
      ( r1_tarski(u1_struct_0(A_37),k2_pre_topc(A_37,u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_31,c_143])).

tff(c_158,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_152])).

tff(c_164,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56,c_158])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_224,plain,(
    ! [B_44] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_44),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56,c_203])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k3_subset_1(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_276,plain,(
    ! [B_51] :
      ( k4_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_51)) = k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_224,c_10])).

tff(c_283,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) = k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_31,c_276])).

tff(c_286,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_283])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k2_subset_1(A_8) = B_9
      | ~ r1_tarski(k3_subset_1(A_8,B_9),B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(k3_subset_1(A_8,B_9),B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_290,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k1_xboole_0,k2_pre_topc('#skF_1',k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_32])).

tff(c_294,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_290])).

tff(c_295,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_294])).

tff(c_311,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_207,c_295])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.35  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 2.26/1.35  
% 2.26/1.35  %Foreground sorts:
% 2.26/1.35  
% 2.26/1.35  
% 2.26/1.35  %Background operators:
% 2.26/1.35  
% 2.26/1.35  
% 2.26/1.35  %Foreground operators:
% 2.26/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.26/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.26/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.26/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.26/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.26/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.26/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.35  
% 2.26/1.36  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.26/1.36  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.26/1.36  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.26/1.36  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.26/1.36  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.26/1.36  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.26/1.36  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.26/1.36  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.26/1.36  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.26/1.36  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.26/1.36  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.26/1.36  tff(c_8, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.36  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.26/1.36  tff(c_31, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.26/1.36  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.26/1.36  tff(c_22, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.36  tff(c_47, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.36  tff(c_52, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_22, c_47])).
% 2.26/1.36  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.26/1.36  tff(c_195, plain, (![A_39, B_40]: (m1_subset_1(k2_pre_topc(A_39, B_40), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.36  tff(c_203, plain, (![B_40]: (m1_subset_1(k2_pre_topc('#skF_1', B_40), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_195])).
% 2.26/1.36  tff(c_207, plain, (![B_40]: (m1_subset_1(k2_pre_topc('#skF_1', B_40), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56, c_203])).
% 2.26/1.36  tff(c_26, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.26/1.36  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.36  tff(c_143, plain, (![B_35, A_36]: (r1_tarski(B_35, k2_pre_topc(A_36, B_35)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.36  tff(c_152, plain, (![A_37]: (r1_tarski(u1_struct_0(A_37), k2_pre_topc(A_37, u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_31, c_143])).
% 2.26/1.36  tff(c_158, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_152])).
% 2.26/1.36  tff(c_164, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56, c_158])).
% 2.26/1.36  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.36  tff(c_170, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_4])).
% 2.26/1.36  tff(c_224, plain, (![B_44]: (m1_subset_1(k2_pre_topc('#skF_1', B_44), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56, c_203])).
% 2.26/1.36  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k3_subset_1(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.36  tff(c_276, plain, (![B_51]: (k4_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_51))=k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_224, c_10])).
% 2.26/1.36  tff(c_283, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))=k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_31, c_276])).
% 2.26/1.36  tff(c_286, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_283])).
% 2.26/1.36  tff(c_16, plain, (![A_8, B_9]: (k2_subset_1(A_8)=B_9 | ~r1_tarski(k3_subset_1(A_8, B_9), B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.36  tff(c_32, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(k3_subset_1(A_8, B_9), B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 2.26/1.36  tff(c_290, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k1_xboole_0, k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_286, c_32])).
% 2.26/1.36  tff(c_294, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_290])).
% 2.26/1.36  tff(c_295, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_26, c_294])).
% 2.26/1.36  tff(c_311, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_207, c_295])).
% 2.26/1.36  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_311])).
% 2.26/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  
% 2.26/1.36  Inference rules
% 2.26/1.36  ----------------------
% 2.26/1.36  #Ref     : 0
% 2.26/1.36  #Sup     : 63
% 2.26/1.36  #Fact    : 0
% 2.26/1.36  #Define  : 0
% 2.26/1.36  #Split   : 0
% 2.26/1.36  #Chain   : 0
% 2.26/1.36  #Close   : 0
% 2.26/1.36  
% 2.26/1.36  Ordering : KBO
% 2.26/1.36  
% 2.26/1.36  Simplification rules
% 2.26/1.36  ----------------------
% 2.26/1.36  #Subsume      : 1
% 2.26/1.36  #Demod        : 37
% 2.26/1.36  #Tautology    : 35
% 2.26/1.36  #SimpNegUnit  : 1
% 2.26/1.36  #BackRed      : 0
% 2.26/1.36  
% 2.26/1.36  #Partial instantiations: 0
% 2.26/1.36  #Strategies tried      : 1
% 2.26/1.36  
% 2.26/1.36  Timing (in seconds)
% 2.26/1.36  ----------------------
% 2.26/1.36  Preprocessing        : 0.32
% 2.26/1.36  Parsing              : 0.17
% 2.26/1.36  CNF conversion       : 0.02
% 2.26/1.36  Main loop            : 0.20
% 2.26/1.36  Inferencing          : 0.08
% 2.26/1.36  Reduction            : 0.07
% 2.26/1.36  Demodulation         : 0.05
% 2.26/1.36  BG Simplification    : 0.01
% 2.26/1.36  Subsumption          : 0.03
% 2.26/1.36  Abstraction          : 0.01
% 2.26/1.36  MUC search           : 0.00
% 2.26/1.36  Cooper               : 0.00
% 2.26/1.36  Total                : 0.56
% 2.26/1.36  Index Insertion      : 0.00
% 2.26/1.36  Index Deletion       : 0.00
% 2.26/1.36  Index Matching       : 0.00
% 2.26/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
