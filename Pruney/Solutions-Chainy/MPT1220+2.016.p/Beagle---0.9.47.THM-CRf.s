%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:23 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   54 (  86 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 123 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_228,plain,(
    ! [A_53,B_54] :
      ( k4_subset_1(u1_struct_0(A_53),B_54,k3_subset_1(u1_struct_0(A_53),B_54)) = k2_struct_0(A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_subset_1(A_7,B_8,k3_subset_1(A_7,B_8)) = k2_subset_1(A_7)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [A_33,B_34] :
      ( k4_subset_1(A_33,B_34,k3_subset_1(A_33,B_34)) = A_33
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_85,plain,(
    ! [A_33] : k4_subset_1(A_33,'#skF_1'(k1_zfmisc_1(A_33)),k3_subset_1(A_33,'#skF_1'(k1_zfmisc_1(A_33)))) = A_33 ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_235,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ m1_subset_1('#skF_1'(k1_zfmisc_1(u1_struct_0(A_53))),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_85])).

tff(c_268,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_273,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_22,c_268])).

tff(c_277,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_273])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_160,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k2_pre_topc(A_44,B_45),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k2_pre_topc(A_44,B_45),u1_struct_0(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_160,c_16])).

tff(c_117,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(B_38,k2_pre_topc(A_39,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_130,plain,(
    ! [A_40] :
      ( r1_tarski(u1_struct_0(A_40),k2_pre_topc(A_40,u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_49] :
      ( k2_pre_topc(A_49,u1_struct_0(A_49)) = u1_struct_0(A_49)
      | ~ r1_tarski(k2_pre_topc(A_49,u1_struct_0(A_49)),u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_183,plain,(
    ! [A_44] :
      ( k2_pre_topc(A_44,u1_struct_0(A_44)) = u1_struct_0(A_44)
      | ~ m1_subset_1(u1_struct_0(A_44),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_170,c_179])).

tff(c_186,plain,(
    ! [A_44] :
      ( k2_pre_topc(A_44,u1_struct_0(A_44)) = u1_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_183])).

tff(c_287,plain,
    ( k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_186])).

tff(c_313,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_277,c_287])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:27:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.17/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.17/1.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.17/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.17/1.29  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.17/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.29  
% 2.17/1.30  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 2.17/1.30  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.17/1.30  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.17/1.30  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.17/1.30  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.17/1.30  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.17/1.30  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.17/1.30  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.17/1.30  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.30  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.17/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.30  tff(c_28, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.30  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.30  tff(c_22, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.30  tff(c_12, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.30  tff(c_228, plain, (![A_53, B_54]: (k4_subset_1(u1_struct_0(A_53), B_54, k3_subset_1(u1_struct_0(A_53), B_54))=k2_struct_0(A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.17/1.30  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_14, plain, (![A_7, B_8]: (k4_subset_1(A_7, B_8, k3_subset_1(A_7, B_8))=k2_subset_1(A_7) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_75, plain, (![A_33, B_34]: (k4_subset_1(A_33, B_34, k3_subset_1(A_33, B_34))=A_33 | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.17/1.30  tff(c_85, plain, (![A_33]: (k4_subset_1(A_33, '#skF_1'(k1_zfmisc_1(A_33)), k3_subset_1(A_33, '#skF_1'(k1_zfmisc_1(A_33))))=A_33)), inference(resolution, [status(thm)], [c_12, c_75])).
% 2.17/1.30  tff(c_235, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~m1_subset_1('#skF_1'(k1_zfmisc_1(u1_struct_0(A_53))), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_228, c_85])).
% 2.17/1.30  tff(c_268, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_235])).
% 2.17/1.30  tff(c_273, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_22, c_268])).
% 2.17/1.30  tff(c_277, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_273])).
% 2.17/1.30  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.30  tff(c_32, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.17/1.30  tff(c_160, plain, (![A_44, B_45]: (m1_subset_1(k2_pre_topc(A_44, B_45), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.30  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_170, plain, (![A_44, B_45]: (r1_tarski(k2_pre_topc(A_44, B_45), u1_struct_0(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_160, c_16])).
% 2.17/1.30  tff(c_117, plain, (![B_38, A_39]: (r1_tarski(B_38, k2_pre_topc(A_39, B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.30  tff(c_130, plain, (![A_40]: (r1_tarski(u1_struct_0(A_40), k2_pre_topc(A_40, u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_32, c_117])).
% 2.17/1.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.30  tff(c_179, plain, (![A_49]: (k2_pre_topc(A_49, u1_struct_0(A_49))=u1_struct_0(A_49) | ~r1_tarski(k2_pre_topc(A_49, u1_struct_0(A_49)), u1_struct_0(A_49)) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_130, c_2])).
% 2.17/1.30  tff(c_183, plain, (![A_44]: (k2_pre_topc(A_44, u1_struct_0(A_44))=u1_struct_0(A_44) | ~m1_subset_1(u1_struct_0(A_44), k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_170, c_179])).
% 2.17/1.30  tff(c_186, plain, (![A_44]: (k2_pre_topc(A_44, u1_struct_0(A_44))=u1_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_183])).
% 2.17/1.30  tff(c_287, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_277, c_186])).
% 2.17/1.30  tff(c_313, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_277, c_287])).
% 2.17/1.30  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_313])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 61
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 0
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 7
% 2.17/1.30  #Demod        : 31
% 2.17/1.30  #Tautology    : 25
% 2.17/1.30  #SimpNegUnit  : 1
% 2.17/1.30  #BackRed      : 0
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.31  Preprocessing        : 0.29
% 2.17/1.31  Parsing              : 0.17
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.20
% 2.17/1.31  Inferencing          : 0.08
% 2.17/1.31  Reduction            : 0.06
% 2.17/1.31  Demodulation         : 0.04
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.04
% 2.17/1.31  Abstraction          : 0.01
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.52
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
