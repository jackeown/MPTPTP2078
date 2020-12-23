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
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 188 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  109 ( 317 expanded)
%              Number of equality atoms :   40 ( 115 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_51,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_119,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k3_subset_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_136,plain,(
    ! [B_41,A_42] :
      ( k4_xboole_0(B_41,A_42) = k3_subset_1(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_142,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_145,plain,(
    ! [B_2] : k3_subset_1(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_142])).

tff(c_153,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [B_46,A_47] :
      ( k3_subset_1(B_46,k3_subset_1(B_46,A_47)) = A_47
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_172,plain,(
    ! [B_2] :
      ( k3_subset_1(B_2,k1_xboole_0) = B_2
      | ~ r1_tarski(B_2,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_157])).

tff(c_190,plain,(
    ! [B_50] : k3_subset_1(B_50,k1_xboole_0) = B_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_21] :
      ( k1_struct_0(A_21) = k1_xboole_0
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_41,plain,(
    ! [A_22] :
      ( k1_struct_0(A_22) = k1_xboole_0
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_24,c_36])).

tff(c_45,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_83,plain,(
    ! [A_34] :
      ( k3_subset_1(u1_struct_0(A_34),k1_struct_0(A_34)) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_92,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_83])).

tff(c_95,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_103,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_103])).

tff(c_108,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_203,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_108])).

tff(c_278,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k2_pre_topc(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_291,plain,(
    ! [B_59] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_59),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_278])).

tff(c_326,plain,(
    ! [B_62] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_62),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_203,c_291])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_341,plain,(
    ! [B_63] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_63),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_326,c_16])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_439,plain,(
    ! [B_68] :
      ( k4_xboole_0(k2_pre_topc('#skF_1',B_68),k2_struct_0('#skF_1')) = k1_xboole_0
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_341,c_10])).

tff(c_473,plain,(
    ! [A_71] :
      ( k4_xboole_0(k2_pre_topc('#skF_1',A_71),k2_struct_0('#skF_1')) = k1_xboole_0
      | ~ r1_tarski(A_71,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_439])).

tff(c_30,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [B_18,A_16] :
      ( r1_tarski(B_18,k2_pre_topc(A_16,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_223,plain,(
    ! [B_18] :
      ( r1_tarski(B_18,k2_pre_topc('#skF_1',B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_28])).

tff(c_248,plain,(
    ! [B_55] :
      ( r1_tarski(B_55,k2_pre_topc('#skF_1',B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_223])).

tff(c_253,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,k2_pre_topc('#skF_1',A_56))
      | ~ r1_tarski(A_56,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_248])).

tff(c_269,plain,(
    ! [A_57] :
      ( k4_xboole_0(A_57,k2_pre_topc('#skF_1',A_57)) = k1_xboole_0
      | ~ r1_tarski(A_57,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_253,c_10])).

tff(c_277,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | k4_xboole_0(A_40,B_39) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_131,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k4_xboole_0(B_4,A_3) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_300,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | k4_xboole_0(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_131])).

tff(c_307,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_300])).

tff(c_479,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_307])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.39  
% 2.40/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.40  %$ r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.40/1.40  
% 2.40/1.40  %Foreground sorts:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Background operators:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Foreground operators:
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.40/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.40  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.40/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.40/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.40/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.40  
% 2.40/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.41  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.40/1.41  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.40/1.41  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.40/1.41  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.40/1.41  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.40/1.41  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.40/1.41  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.40/1.41  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.40/1.41  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.40/1.41  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.40/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.41  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.41  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.40/1.41  tff(c_51, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.41  tff(c_55, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_51])).
% 2.40/1.41  tff(c_119, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k3_subset_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.41  tff(c_136, plain, (![B_41, A_42]: (k4_xboole_0(B_41, A_42)=k3_subset_1(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(resolution, [status(thm)], [c_18, c_119])).
% 2.40/1.41  tff(c_142, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.40/1.41  tff(c_145, plain, (![B_2]: (k3_subset_1(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_142])).
% 2.40/1.41  tff(c_153, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.40/1.41  tff(c_157, plain, (![B_46, A_47]: (k3_subset_1(B_46, k3_subset_1(B_46, A_47))=A_47 | ~r1_tarski(A_47, B_46))), inference(resolution, [status(thm)], [c_18, c_153])).
% 2.40/1.41  tff(c_172, plain, (![B_2]: (k3_subset_1(B_2, k1_xboole_0)=B_2 | ~r1_tarski(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_145, c_157])).
% 2.40/1.41  tff(c_190, plain, (![B_50]: (k3_subset_1(B_50, k1_xboole_0)=B_50)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_172])).
% 2.40/1.41  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.41  tff(c_36, plain, (![A_21]: (k1_struct_0(A_21)=k1_xboole_0 | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.40/1.41  tff(c_41, plain, (![A_22]: (k1_struct_0(A_22)=k1_xboole_0 | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_24, c_36])).
% 2.40/1.41  tff(c_45, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.40/1.41  tff(c_83, plain, (![A_34]: (k3_subset_1(u1_struct_0(A_34), k1_struct_0(A_34))=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.41  tff(c_92, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45, c_83])).
% 2.40/1.41  tff(c_95, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_92])).
% 2.40/1.41  tff(c_103, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_95])).
% 2.40/1.41  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_103])).
% 2.40/1.41  tff(c_108, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_92])).
% 2.40/1.41  tff(c_203, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_190, c_108])).
% 2.40/1.41  tff(c_278, plain, (![A_58, B_59]: (m1_subset_1(k2_pre_topc(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.40/1.41  tff(c_291, plain, (![B_59]: (m1_subset_1(k2_pre_topc('#skF_1', B_59), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_278])).
% 2.40/1.41  tff(c_326, plain, (![B_62]: (m1_subset_1(k2_pre_topc('#skF_1', B_62), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_203, c_291])).
% 2.40/1.41  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.41  tff(c_341, plain, (![B_63]: (r1_tarski(k2_pre_topc('#skF_1', B_63), k2_struct_0('#skF_1')) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_326, c_16])).
% 2.40/1.41  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.41  tff(c_439, plain, (![B_68]: (k4_xboole_0(k2_pre_topc('#skF_1', B_68), k2_struct_0('#skF_1'))=k1_xboole_0 | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_341, c_10])).
% 2.40/1.41  tff(c_473, plain, (![A_71]: (k4_xboole_0(k2_pre_topc('#skF_1', A_71), k2_struct_0('#skF_1'))=k1_xboole_0 | ~r1_tarski(A_71, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_439])).
% 2.40/1.41  tff(c_30, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.40/1.41  tff(c_28, plain, (![B_18, A_16]: (r1_tarski(B_18, k2_pre_topc(A_16, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.40/1.41  tff(c_223, plain, (![B_18]: (r1_tarski(B_18, k2_pre_topc('#skF_1', B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_28])).
% 2.40/1.41  tff(c_248, plain, (![B_55]: (r1_tarski(B_55, k2_pre_topc('#skF_1', B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_223])).
% 2.40/1.41  tff(c_253, plain, (![A_56]: (r1_tarski(A_56, k2_pre_topc('#skF_1', A_56)) | ~r1_tarski(A_56, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_248])).
% 2.40/1.41  tff(c_269, plain, (![A_57]: (k4_xboole_0(A_57, k2_pre_topc('#skF_1', A_57))=k1_xboole_0 | ~r1_tarski(A_57, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_253, c_10])).
% 2.40/1.41  tff(c_277, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_269])).
% 2.40/1.41  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.41  tff(c_73, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.41  tff(c_124, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | k4_xboole_0(A_40, B_39)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_73])).
% 2.40/1.41  tff(c_131, plain, (![B_4, A_3]: (B_4=A_3 | k4_xboole_0(B_4, A_3)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_124])).
% 2.40/1.41  tff(c_300, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | k4_xboole_0(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_277, c_131])).
% 2.40/1.41  tff(c_307, plain, (k4_xboole_0(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_300])).
% 2.40/1.41  tff(c_479, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_307])).
% 2.40/1.41  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_479])).
% 2.40/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.41  
% 2.40/1.41  Inference rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Ref     : 0
% 2.40/1.41  #Sup     : 107
% 2.40/1.41  #Fact    : 0
% 2.40/1.41  #Define  : 0
% 2.40/1.41  #Split   : 1
% 2.40/1.41  #Chain   : 0
% 2.40/1.41  #Close   : 0
% 2.40/1.41  
% 2.40/1.41  Ordering : KBO
% 2.40/1.41  
% 2.40/1.41  Simplification rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Subsume      : 2
% 2.40/1.41  #Demod        : 41
% 2.40/1.41  #Tautology    : 46
% 2.40/1.41  #SimpNegUnit  : 1
% 2.40/1.41  #BackRed      : 1
% 2.40/1.41  
% 2.40/1.41  #Partial instantiations: 0
% 2.40/1.41  #Strategies tried      : 1
% 2.40/1.41  
% 2.40/1.41  Timing (in seconds)
% 2.40/1.41  ----------------------
% 2.40/1.42  Preprocessing        : 0.30
% 2.40/1.42  Parsing              : 0.16
% 2.40/1.42  CNF conversion       : 0.02
% 2.40/1.42  Main loop            : 0.25
% 2.40/1.42  Inferencing          : 0.09
% 2.40/1.42  Reduction            : 0.07
% 2.40/1.42  Demodulation         : 0.05
% 2.40/1.42  BG Simplification    : 0.01
% 2.40/1.42  Subsumption          : 0.05
% 2.40/1.42  Abstraction          : 0.02
% 2.40/1.42  MUC search           : 0.00
% 2.40/1.42  Cooper               : 0.00
% 2.40/1.42  Total                : 0.59
% 2.40/1.42  Index Insertion      : 0.00
% 2.40/1.42  Index Deletion       : 0.00
% 2.40/1.42  Index Matching       : 0.00
% 2.40/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
