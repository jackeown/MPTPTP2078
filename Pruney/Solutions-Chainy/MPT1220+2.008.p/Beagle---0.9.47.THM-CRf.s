%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 305 expanded)
%              Number of leaves         :   28 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  108 ( 547 expanded)
%              Number of equality atoms :   16 ( 133 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_27] :
      ( k1_struct_0(A_27) = k1_xboole_0
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    ! [A_28] :
      ( k1_struct_0(A_28) = k1_xboole_0
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_49,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_97,plain,(
    ! [A_38] :
      ( k3_subset_1(u1_struct_0(A_38),k1_struct_0(A_38)) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_106,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_97])).

tff(c_109,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_112,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_109])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112])).

tff(c_118,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [C_57,A_58,B_59] :
      ( r1_tarski(C_57,k3_subset_1(A_58,B_59))
      | ~ r1_tarski(B_59,k3_subset_1(A_58,C_57))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_184,plain,(
    ! [C_57,A_58] :
      ( r1_tarski(C_57,k3_subset_1(A_58,k1_xboole_0))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_8,c_174])).

tff(c_191,plain,(
    ! [C_60,A_61] :
      ( r1_tarski(C_60,k3_subset_1(A_61,k1_xboole_0))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_184])).

tff(c_203,plain,(
    ! [C_62] :
      ( r1_tarski(C_62,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_191])).

tff(c_229,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_63,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_203])).

tff(c_245,plain,(
    r1_tarski(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_88,plain,(
    ! [A_36] :
      ( m1_subset_1(k2_struct_0(A_36),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_37] :
      ( r1_tarski(k2_struct_0(A_37),u1_struct_0(A_37))
      | ~ l1_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_88,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ r1_tarski(u1_struct_0(A_37),k2_struct_0(A_37))
      | ~ l1_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_250,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_245,c_96])).

tff(c_255,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_250])).

tff(c_24,plain,(
    ! [A_17] :
      ( m1_subset_1(k2_struct_0(A_17),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_279,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_24])).

tff(c_293,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_279])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_pre_topc(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_207,plain,(
    ! [B_16] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_16),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_222,plain,(
    ! [B_16] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_16),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_207])).

tff(c_324,plain,(
    ! [B_16] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_16),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_222])).

tff(c_32,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    ! [B_22,A_20] :
      ( r1_tarski(B_22,k2_pre_topc(A_20,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_267,plain,(
    ! [B_22] :
      ( r1_tarski(B_22,k2_pre_topc('#skF_1',B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_30])).

tff(c_332,plain,(
    ! [B_68] :
      ( r1_tarski(B_68,k2_pre_topc('#skF_1',B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_267])).

tff(c_341,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_293,c_332])).

tff(c_346,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_349,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_346])).

tff(c_352,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_324,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.08/1.30  
% 2.08/1.30  %Foreground sorts:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Background operators:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Foreground operators:
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.08/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.08/1.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.08/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.30  
% 2.08/1.31  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 2.08/1.31  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.08/1.31  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.08/1.31  tff(f_76, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.08/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.31  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.31  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.08/1.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.08/1.31  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.08/1.31  tff(f_68, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.08/1.31  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.08/1.31  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.08/1.31  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.31  tff(c_26, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.31  tff(c_40, plain, (![A_27]: (k1_struct_0(A_27)=k1_xboole_0 | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.31  tff(c_45, plain, (![A_28]: (k1_struct_0(A_28)=k1_xboole_0 | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_26, c_40])).
% 2.08/1.31  tff(c_49, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.08/1.31  tff(c_97, plain, (![A_38]: (k3_subset_1(u1_struct_0(A_38), k1_struct_0(A_38))=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.31  tff(c_106, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_97])).
% 2.08/1.31  tff(c_109, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_106])).
% 2.08/1.31  tff(c_112, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_109])).
% 2.08/1.31  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_112])).
% 2.08/1.31  tff(c_118, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_106])).
% 2.08/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.31  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.31  tff(c_117, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_106])).
% 2.08/1.31  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.31  tff(c_174, plain, (![C_57, A_58, B_59]: (r1_tarski(C_57, k3_subset_1(A_58, B_59)) | ~r1_tarski(B_59, k3_subset_1(A_58, C_57)) | ~m1_subset_1(C_57, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.31  tff(c_184, plain, (![C_57, A_58]: (r1_tarski(C_57, k3_subset_1(A_58, k1_xboole_0)) | ~m1_subset_1(C_57, k1_zfmisc_1(A_58)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_58)))), inference(resolution, [status(thm)], [c_8, c_174])).
% 2.08/1.31  tff(c_191, plain, (![C_60, A_61]: (r1_tarski(C_60, k3_subset_1(A_61, k1_xboole_0)) | ~m1_subset_1(C_60, k1_zfmisc_1(A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_184])).
% 2.08/1.31  tff(c_203, plain, (![C_62]: (r1_tarski(C_62, k2_struct_0('#skF_1')) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_117, c_191])).
% 2.08/1.31  tff(c_229, plain, (![A_63]: (r1_tarski(A_63, k2_struct_0('#skF_1')) | ~r1_tarski(A_63, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_203])).
% 2.08/1.31  tff(c_245, plain, (r1_tarski(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_229])).
% 2.08/1.31  tff(c_88, plain, (![A_36]: (m1_subset_1(k2_struct_0(A_36), k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.31  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.31  tff(c_93, plain, (![A_37]: (r1_tarski(k2_struct_0(A_37), u1_struct_0(A_37)) | ~l1_struct_0(A_37))), inference(resolution, [status(thm)], [c_88, c_14])).
% 2.08/1.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.31  tff(c_96, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~r1_tarski(u1_struct_0(A_37), k2_struct_0(A_37)) | ~l1_struct_0(A_37))), inference(resolution, [status(thm)], [c_93, c_2])).
% 2.08/1.31  tff(c_250, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_245, c_96])).
% 2.08/1.31  tff(c_255, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_250])).
% 2.08/1.31  tff(c_24, plain, (![A_17]: (m1_subset_1(k2_struct_0(A_17), k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.31  tff(c_279, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_255, c_24])).
% 2.08/1.31  tff(c_293, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_279])).
% 2.08/1.31  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(k2_pre_topc(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.31  tff(c_207, plain, (![B_16]: (r1_tarski(k2_pre_topc('#skF_1', B_16), k2_struct_0('#skF_1')) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_203])).
% 2.08/1.31  tff(c_222, plain, (![B_16]: (r1_tarski(k2_pre_topc('#skF_1', B_16), k2_struct_0('#skF_1')) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_207])).
% 2.08/1.31  tff(c_324, plain, (![B_16]: (r1_tarski(k2_pre_topc('#skF_1', B_16), k2_struct_0('#skF_1')) | ~m1_subset_1(B_16, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_222])).
% 2.08/1.31  tff(c_32, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.31  tff(c_30, plain, (![B_22, A_20]: (r1_tarski(B_22, k2_pre_topc(A_20, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.08/1.31  tff(c_267, plain, (![B_22]: (r1_tarski(B_22, k2_pre_topc('#skF_1', B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_30])).
% 2.08/1.31  tff(c_332, plain, (![B_68]: (r1_tarski(B_68, k2_pre_topc('#skF_1', B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_267])).
% 2.08/1.31  tff(c_341, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_293, c_332])).
% 2.08/1.31  tff(c_346, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_341, c_2])).
% 2.08/1.31  tff(c_349, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_32, c_346])).
% 2.08/1.31  tff(c_352, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_324, c_349])).
% 2.08/1.31  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_352])).
% 2.08/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  Inference rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Ref     : 0
% 2.08/1.31  #Sup     : 68
% 2.08/1.31  #Fact    : 0
% 2.08/1.31  #Define  : 0
% 2.08/1.31  #Split   : 1
% 2.08/1.31  #Chain   : 0
% 2.08/1.31  #Close   : 0
% 2.08/1.31  
% 2.08/1.31  Ordering : KBO
% 2.08/1.31  
% 2.08/1.31  Simplification rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Subsume      : 2
% 2.08/1.31  #Demod        : 47
% 2.08/1.31  #Tautology    : 33
% 2.08/1.31  #SimpNegUnit  : 1
% 2.08/1.31  #BackRed      : 3
% 2.08/1.31  
% 2.08/1.31  #Partial instantiations: 0
% 2.08/1.31  #Strategies tried      : 1
% 2.08/1.31  
% 2.08/1.31  Timing (in seconds)
% 2.08/1.31  ----------------------
% 2.08/1.32  Preprocessing        : 0.29
% 2.08/1.32  Parsing              : 0.16
% 2.08/1.32  CNF conversion       : 0.02
% 2.08/1.32  Main loop            : 0.24
% 2.08/1.32  Inferencing          : 0.09
% 2.08/1.32  Reduction            : 0.07
% 2.08/1.32  Demodulation         : 0.05
% 2.08/1.32  BG Simplification    : 0.01
% 2.08/1.32  Subsumption          : 0.04
% 2.08/1.32  Abstraction          : 0.01
% 2.08/1.32  MUC search           : 0.00
% 2.08/1.32  Cooper               : 0.00
% 2.08/1.32  Total                : 0.56
% 2.08/1.32  Index Insertion      : 0.00
% 2.08/1.32  Index Deletion       : 0.00
% 2.08/1.32  Index Matching       : 0.00
% 2.08/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
