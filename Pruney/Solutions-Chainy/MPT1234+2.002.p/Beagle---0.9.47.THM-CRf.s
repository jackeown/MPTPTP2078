%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:35 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 164 expanded)
%              Number of leaves         :   20 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 338 expanded)
%              Number of equality atoms :    7 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_16,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21,plain,(
    ! [A_18,B_19] :
      ( k3_subset_1(A_18,k3_subset_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_142,plain,(
    ! [A_38,B_39] :
      ( k3_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,k3_subset_1(u1_struct_0(A_38),B_39))) = k1_tops_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_185,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_142])).

tff(c_189,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_185])).

tff(c_234,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_237,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_237])).

tff(c_243,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(B_22,k2_pre_topc(A_23,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_23,B_2] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_23),B_2),k2_pre_topc(A_23,k3_subset_1(u1_struct_0(A_23),B_2)))
      | ~ l1_pre_topc(A_23)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_23))) ) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_54,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(k3_subset_1(A_26,C_27),k3_subset_1(A_26,B_28))
      | ~ r1_tarski(B_28,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [C_27] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_27),'#skF_2')
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_54])).

tff(c_634,plain,(
    ! [C_49] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_49),'#skF_2')
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_60])).

tff(c_639,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_43,c_634])).

tff(c_646,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_639])).

tff(c_650,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_653,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_650])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_243,c_653])).

tff(c_659,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_12,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(B_13,k2_pre_topc(A_11,B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_245,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_243,c_12])).

tff(c_250,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_245])).

tff(c_8,plain,(
    ! [A_5,C_8,B_6] :
      ( r1_tarski(k3_subset_1(A_5,C_8),k3_subset_1(A_5,B_6))
      | ~ r1_tarski(B_6,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_688,plain,(
    ! [A_50,B_51,B_52] :
      ( r1_tarski(k1_tops_1(A_50,B_51),k3_subset_1(u1_struct_0(A_50),B_52))
      | ~ r1_tarski(B_52,k2_pre_topc(A_50,k3_subset_1(u1_struct_0(A_50),B_51)))
      | ~ m1_subset_1(k2_pre_topc(A_50,k3_subset_1(u1_struct_0(A_50),B_51)),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_8])).

tff(c_698,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_250,c_688])).

tff(c_720,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_243,c_659,c_24,c_698])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.50  
% 2.96/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.50  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.96/1.50  
% 2.96/1.50  %Foreground sorts:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Background operators:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Foreground operators:
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.96/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.96/1.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.96/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.96/1.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.96/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.50  
% 2.96/1.52  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.96/1.52  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.96/1.52  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.96/1.52  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.96/1.52  tff(f_48, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.96/1.52  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.96/1.52  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.96/1.52  tff(c_16, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.52  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.52  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.52  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.52  tff(c_21, plain, (![A_18, B_19]: (k3_subset_1(A_18, k3_subset_1(A_18, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.52  tff(c_24, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_21])).
% 2.96/1.52  tff(c_142, plain, (![A_38, B_39]: (k3_subset_1(u1_struct_0(A_38), k2_pre_topc(A_38, k3_subset_1(u1_struct_0(A_38), B_39)))=k1_tops_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.96/1.52  tff(c_185, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_142])).
% 2.96/1.52  tff(c_189, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_185])).
% 2.96/1.52  tff(c_234, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_189])).
% 2.96/1.52  tff(c_237, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_234])).
% 2.96/1.52  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_237])).
% 2.96/1.52  tff(c_243, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_189])).
% 2.96/1.52  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(k2_pre_topc(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.52  tff(c_37, plain, (![B_22, A_23]: (r1_tarski(B_22, k2_pre_topc(A_23, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.96/1.52  tff(c_43, plain, (![A_23, B_2]: (r1_tarski(k3_subset_1(u1_struct_0(A_23), B_2), k2_pre_topc(A_23, k3_subset_1(u1_struct_0(A_23), B_2))) | ~l1_pre_topc(A_23) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_23))))), inference(resolution, [status(thm)], [c_2, c_37])).
% 2.96/1.52  tff(c_54, plain, (![A_26, C_27, B_28]: (r1_tarski(k3_subset_1(A_26, C_27), k3_subset_1(A_26, B_28)) | ~r1_tarski(B_28, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.52  tff(c_60, plain, (![C_27]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_27), '#skF_2') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_54])).
% 2.96/1.52  tff(c_634, plain, (![C_49]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_49), '#skF_2') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_60])).
% 2.96/1.52  tff(c_639, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_43, c_634])).
% 2.96/1.52  tff(c_646, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_639])).
% 2.96/1.52  tff(c_650, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_646])).
% 2.96/1.52  tff(c_653, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_650])).
% 2.96/1.52  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_243, c_653])).
% 2.96/1.52  tff(c_659, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_646])).
% 2.96/1.52  tff(c_12, plain, (![B_13, A_11]: (r1_tarski(B_13, k2_pre_topc(A_11, B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.96/1.52  tff(c_245, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_243, c_12])).
% 2.96/1.52  tff(c_250, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_245])).
% 2.96/1.52  tff(c_8, plain, (![A_5, C_8, B_6]: (r1_tarski(k3_subset_1(A_5, C_8), k3_subset_1(A_5, B_6)) | ~r1_tarski(B_6, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.52  tff(c_688, plain, (![A_50, B_51, B_52]: (r1_tarski(k1_tops_1(A_50, B_51), k3_subset_1(u1_struct_0(A_50), B_52)) | ~r1_tarski(B_52, k2_pre_topc(A_50, k3_subset_1(u1_struct_0(A_50), B_51))) | ~m1_subset_1(k2_pre_topc(A_50, k3_subset_1(u1_struct_0(A_50), B_51)), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(superposition, [status(thm), theory('equality')], [c_142, c_8])).
% 2.96/1.52  tff(c_698, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_250, c_688])).
% 2.96/1.52  tff(c_720, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_243, c_659, c_24, c_698])).
% 2.96/1.52  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_720])).
% 2.96/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.52  
% 2.96/1.52  Inference rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Ref     : 0
% 2.96/1.52  #Sup     : 172
% 2.96/1.52  #Fact    : 0
% 2.96/1.52  #Define  : 0
% 2.96/1.52  #Split   : 6
% 2.96/1.52  #Chain   : 0
% 2.96/1.52  #Close   : 0
% 2.96/1.52  
% 2.96/1.52  Ordering : KBO
% 2.96/1.52  
% 2.96/1.52  Simplification rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Subsume      : 4
% 2.96/1.52  #Demod        : 134
% 2.96/1.52  #Tautology    : 39
% 2.96/1.52  #SimpNegUnit  : 1
% 2.96/1.52  #BackRed      : 0
% 2.96/1.52  
% 2.96/1.52  #Partial instantiations: 0
% 2.96/1.52  #Strategies tried      : 1
% 2.96/1.52  
% 2.96/1.52  Timing (in seconds)
% 2.96/1.52  ----------------------
% 2.96/1.52  Preprocessing        : 0.26
% 2.96/1.52  Parsing              : 0.14
% 2.96/1.52  CNF conversion       : 0.02
% 2.96/1.52  Main loop            : 0.40
% 2.96/1.52  Inferencing          : 0.15
% 2.96/1.52  Reduction            : 0.13
% 2.96/1.52  Demodulation         : 0.09
% 2.96/1.52  BG Simplification    : 0.02
% 2.96/1.52  Subsumption          : 0.08
% 2.96/1.52  Abstraction          : 0.02
% 2.96/1.52  MUC search           : 0.00
% 2.96/1.52  Cooper               : 0.00
% 2.96/1.52  Total                : 0.69
% 2.96/1.52  Index Insertion      : 0.00
% 2.96/1.52  Index Deletion       : 0.00
% 2.96/1.52  Index Matching       : 0.00
% 2.96/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
