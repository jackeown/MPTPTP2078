%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 12.34s
% Output     : CNFRefutation 12.34s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 105 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_58,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2671,plain,(
    ! [A_182,B_183] :
      ( k2_pre_topc(A_182,B_183) = B_183
      | ~ v4_pre_topc(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2685,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_2671])).

tff(c_2691,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2685])).

tff(c_3220,plain,(
    ! [A_213,B_214] :
      ( k4_subset_1(u1_struct_0(A_213),B_214,k2_tops_1(A_213,B_214)) = k2_pre_topc(A_213,B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3230,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3220])).

tff(c_3236,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2691,c_3230])).

tff(c_52,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k2_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2843,plain,(
    ! [A_190,B_191,C_192] :
      ( k4_subset_1(A_190,B_191,C_192) = k2_xboole_0(B_191,C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_27597,plain,(
    ! [A_514,B_515,B_516] :
      ( k4_subset_1(u1_struct_0(A_514),B_515,k2_tops_1(A_514,B_516)) = k2_xboole_0(B_515,k2_tops_1(A_514,B_516))
      | ~ m1_subset_1(B_515,k1_zfmisc_1(u1_struct_0(A_514)))
      | ~ m1_subset_1(B_516,k1_zfmisc_1(u1_struct_0(A_514)))
      | ~ l1_pre_topc(A_514) ) ),
    inference(resolution,[status(thm)],[c_52,c_2843])).

tff(c_27613,plain,(
    ! [B_516] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_516)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_516))
      | ~ m1_subset_1(B_516,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_27597])).

tff(c_35600,plain,(
    ! [B_596] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_596)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_596))
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_27613])).

tff(c_35623,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_35600])).

tff(c_35632,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_35623])).

tff(c_32,plain,(
    ! [B_29,A_28] : k2_tarski(B_29,A_28) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_258,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_288,plain,(
    ! [B_83,A_84] : k3_tarski(k2_tarski(B_83,A_84)) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_258])).

tff(c_34,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_311,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,A_86) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_34])).

tff(c_30,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_332,plain,(
    ! [A_86,B_85] : r1_tarski(A_86,k2_xboole_0(B_85,A_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_30])).

tff(c_35766,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35632,c_332])).

tff(c_35796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_35766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.34/5.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/5.66  
% 12.34/5.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/5.66  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 12.34/5.66  
% 12.34/5.66  %Foreground sorts:
% 12.34/5.66  
% 12.34/5.66  
% 12.34/5.66  %Background operators:
% 12.34/5.66  
% 12.34/5.66  
% 12.34/5.66  %Foreground operators:
% 12.34/5.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.34/5.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.34/5.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 12.34/5.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.34/5.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.34/5.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.34/5.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.34/5.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.34/5.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.34/5.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.34/5.66  tff('#skF_2', type, '#skF_2': $i).
% 12.34/5.66  tff('#skF_1', type, '#skF_1': $i).
% 12.34/5.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.34/5.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 12.34/5.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.34/5.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.34/5.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.34/5.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.34/5.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.34/5.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.34/5.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.34/5.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.34/5.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.34/5.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.34/5.66  
% 12.34/5.68  tff(f_138, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 12.34/5.68  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 12.34/5.68  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 12.34/5.68  tff(f_114, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 12.34/5.68  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.34/5.68  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.34/5.68  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.34/5.68  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.34/5.68  tff(c_58, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.34/5.68  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.34/5.68  tff(c_60, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.34/5.68  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.34/5.68  tff(c_2671, plain, (![A_182, B_183]: (k2_pre_topc(A_182, B_183)=B_183 | ~v4_pre_topc(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.34/5.68  tff(c_2685, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_2671])).
% 12.34/5.68  tff(c_2691, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2685])).
% 12.34/5.68  tff(c_3220, plain, (![A_213, B_214]: (k4_subset_1(u1_struct_0(A_213), B_214, k2_tops_1(A_213, B_214))=k2_pre_topc(A_213, B_214) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.34/5.68  tff(c_3230, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_3220])).
% 12.34/5.68  tff(c_3236, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2691, c_3230])).
% 12.34/5.68  tff(c_52, plain, (![A_46, B_47]: (m1_subset_1(k2_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.34/5.68  tff(c_2843, plain, (![A_190, B_191, C_192]: (k4_subset_1(A_190, B_191, C_192)=k2_xboole_0(B_191, C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.34/5.68  tff(c_27597, plain, (![A_514, B_515, B_516]: (k4_subset_1(u1_struct_0(A_514), B_515, k2_tops_1(A_514, B_516))=k2_xboole_0(B_515, k2_tops_1(A_514, B_516)) | ~m1_subset_1(B_515, k1_zfmisc_1(u1_struct_0(A_514))) | ~m1_subset_1(B_516, k1_zfmisc_1(u1_struct_0(A_514))) | ~l1_pre_topc(A_514))), inference(resolution, [status(thm)], [c_52, c_2843])).
% 12.34/5.68  tff(c_27613, plain, (![B_516]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_516))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_516)) | ~m1_subset_1(B_516, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_27597])).
% 12.34/5.68  tff(c_35600, plain, (![B_596]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_596))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_596)) | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_27613])).
% 12.34/5.68  tff(c_35623, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_35600])).
% 12.34/5.68  tff(c_35632, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3236, c_35623])).
% 12.34/5.68  tff(c_32, plain, (![B_29, A_28]: (k2_tarski(B_29, A_28)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.34/5.68  tff(c_258, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.34/5.68  tff(c_288, plain, (![B_83, A_84]: (k3_tarski(k2_tarski(B_83, A_84))=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_32, c_258])).
% 12.34/5.68  tff(c_34, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.34/5.68  tff(c_311, plain, (![B_85, A_86]: (k2_xboole_0(B_85, A_86)=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_288, c_34])).
% 12.34/5.68  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.34/5.68  tff(c_332, plain, (![A_86, B_85]: (r1_tarski(A_86, k2_xboole_0(B_85, A_86)))), inference(superposition, [status(thm), theory('equality')], [c_311, c_30])).
% 12.34/5.68  tff(c_35766, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35632, c_332])).
% 12.34/5.68  tff(c_35796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_35766])).
% 12.34/5.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/5.68  
% 12.34/5.68  Inference rules
% 12.34/5.68  ----------------------
% 12.34/5.68  #Ref     : 0
% 12.34/5.68  #Sup     : 8658
% 12.34/5.68  #Fact    : 0
% 12.34/5.68  #Define  : 0
% 12.34/5.68  #Split   : 5
% 12.34/5.68  #Chain   : 0
% 12.34/5.68  #Close   : 0
% 12.34/5.68  
% 12.34/5.68  Ordering : KBO
% 12.34/5.68  
% 12.34/5.68  Simplification rules
% 12.34/5.68  ----------------------
% 12.34/5.68  #Subsume      : 687
% 12.34/5.68  #Demod        : 8453
% 12.34/5.68  #Tautology    : 5450
% 12.34/5.68  #SimpNegUnit  : 1
% 12.34/5.68  #BackRed      : 3
% 12.34/5.68  
% 12.34/5.68  #Partial instantiations: 0
% 12.34/5.68  #Strategies tried      : 1
% 12.34/5.68  
% 12.34/5.68  Timing (in seconds)
% 12.34/5.68  ----------------------
% 12.34/5.68  Preprocessing        : 0.35
% 12.34/5.68  Parsing              : 0.19
% 12.34/5.68  CNF conversion       : 0.02
% 12.34/5.68  Main loop            : 4.58
% 12.34/5.68  Inferencing          : 0.77
% 12.34/5.68  Reduction            : 2.57
% 12.34/5.68  Demodulation         : 2.26
% 12.34/5.68  BG Simplification    : 0.09
% 12.34/5.68  Subsumption          : 0.92
% 12.34/5.68  Abstraction          : 0.14
% 12.34/5.68  MUC search           : 0.00
% 12.34/5.68  Cooper               : 0.00
% 12.34/5.68  Total                : 4.95
% 12.34/5.68  Index Insertion      : 0.00
% 12.34/5.68  Index Deletion       : 0.00
% 12.34/5.68  Index Matching       : 0.00
% 12.34/5.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
