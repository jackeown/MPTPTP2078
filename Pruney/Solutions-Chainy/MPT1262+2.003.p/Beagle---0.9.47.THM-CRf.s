%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:37 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 151 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 348 expanded)
%              Number of equality atoms :   21 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & r1_tarski(B,C) )
                 => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_16,c_38])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_128,plain,(
    ! [B_40,A_41] :
      ( v1_tops_1(B_40,A_41)
      | k2_pre_topc(A_41,B_40) != k2_struct_0(A_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_138,plain,(
    ! [B_40] :
      ( v1_tops_1(B_40,'#skF_1')
      | k2_pre_topc('#skF_1',B_40) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_128])).

tff(c_143,plain,(
    ! [B_42] :
      ( v1_tops_1(B_42,'#skF_1')
      | k2_pre_topc('#skF_1',B_42) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_138])).

tff(c_149,plain,
    ( v1_tops_1('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_143])).

tff(c_160,plain,(
    k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_149])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_28,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_184,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,B_45) = k2_struct_0(A_44)
      | ~ v1_tops_1(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_194,plain,(
    ! [B_45] :
      ( k2_pre_topc('#skF_1',B_45) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_45,'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_184])).

tff(c_452,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_1',B_63) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_194])).

tff(c_461,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_452])).

tff(c_471,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_461])).

tff(c_18,plain,(
    ! [A_9,B_13,C_15] :
      ( r1_tarski(k2_pre_topc(A_9,B_13),k2_pre_topc(A_9,C_15))
      | ~ r1_tarski(B_13,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_476,plain,(
    ! [C_15] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_15))
      | ~ r1_tarski('#skF_2',C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_18])).

tff(c_608,plain,(
    ! [C_73] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_73))
      | ~ r1_tarski('#skF_2',C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59,c_56,c_56,c_476])).

tff(c_99,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_pre_topc(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [B_34] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_34),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_99])).

tff(c_109,plain,(
    ! [B_35] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_35),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_56,c_105])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [B_36] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_36),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [B_36] :
      ( k2_pre_topc('#skF_1',B_36) = k2_struct_0('#skF_1')
      | ~ r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_36))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_626,plain,(
    ! [C_74] :
      ( k2_pre_topc('#skF_1',C_74) = k2_struct_0('#skF_1')
      | ~ r1_tarski('#skF_2',C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_608,c_117])).

tff(c_635,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_626])).

tff(c_649,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_635])).

tff(c_651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.36  
% 2.59/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.36  %$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.36  
% 2.59/1.36  %Foreground sorts:
% 2.59/1.36  
% 2.59/1.36  
% 2.59/1.36  %Background operators:
% 2.59/1.36  
% 2.59/1.36  
% 2.59/1.36  %Foreground operators:
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.36  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.59/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.59/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.59/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.36  
% 2.59/1.38  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 2.59/1.38  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.59/1.38  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.59/1.38  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.59/1.38  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 2.59/1.38  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.59/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.59/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.38  tff(c_24, plain, (~v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.38  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.38  tff(c_16, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.38  tff(c_38, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.38  tff(c_52, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_16, c_38])).
% 2.59/1.38  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.59/1.38  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.38  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30])).
% 2.59/1.38  tff(c_128, plain, (![B_40, A_41]: (v1_tops_1(B_40, A_41) | k2_pre_topc(A_41, B_40)!=k2_struct_0(A_41) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.38  tff(c_138, plain, (![B_40]: (v1_tops_1(B_40, '#skF_1') | k2_pre_topc('#skF_1', B_40)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_40, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_128])).
% 2.59/1.38  tff(c_143, plain, (![B_42]: (v1_tops_1(B_42, '#skF_1') | k2_pre_topc('#skF_1', B_42)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_42, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_138])).
% 2.59/1.38  tff(c_149, plain, (v1_tops_1('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_143])).
% 2.59/1.38  tff(c_160, plain, (k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_149])).
% 2.59/1.38  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.38  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.38  tff(c_59, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 2.59/1.38  tff(c_28, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.38  tff(c_184, plain, (![A_44, B_45]: (k2_pre_topc(A_44, B_45)=k2_struct_0(A_44) | ~v1_tops_1(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.38  tff(c_194, plain, (![B_45]: (k2_pre_topc('#skF_1', B_45)=k2_struct_0('#skF_1') | ~v1_tops_1(B_45, '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_184])).
% 2.59/1.38  tff(c_452, plain, (![B_63]: (k2_pre_topc('#skF_1', B_63)=k2_struct_0('#skF_1') | ~v1_tops_1(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_194])).
% 2.59/1.38  tff(c_461, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_59, c_452])).
% 2.59/1.38  tff(c_471, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_461])).
% 2.59/1.38  tff(c_18, plain, (![A_9, B_13, C_15]: (r1_tarski(k2_pre_topc(A_9, B_13), k2_pre_topc(A_9, C_15)) | ~r1_tarski(B_13, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.38  tff(c_476, plain, (![C_15]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_15)) | ~r1_tarski('#skF_2', C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_18])).
% 2.59/1.38  tff(c_608, plain, (![C_73]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_73)) | ~r1_tarski('#skF_2', C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59, c_56, c_56, c_476])).
% 2.59/1.38  tff(c_99, plain, (![A_33, B_34]: (m1_subset_1(k2_pre_topc(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.38  tff(c_105, plain, (![B_34]: (m1_subset_1(k2_pre_topc('#skF_1', B_34), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_99])).
% 2.59/1.38  tff(c_109, plain, (![B_35]: (m1_subset_1(k2_pre_topc('#skF_1', B_35), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_35, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_56, c_105])).
% 2.59/1.38  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.38  tff(c_114, plain, (![B_36]: (r1_tarski(k2_pre_topc('#skF_1', B_36), k2_struct_0('#skF_1')) | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_109, c_8])).
% 2.59/1.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.38  tff(c_117, plain, (![B_36]: (k2_pre_topc('#skF_1', B_36)=k2_struct_0('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_36)) | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_114, c_2])).
% 2.59/1.38  tff(c_626, plain, (![C_74]: (k2_pre_topc('#skF_1', C_74)=k2_struct_0('#skF_1') | ~r1_tarski('#skF_2', C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_608, c_117])).
% 2.59/1.38  tff(c_635, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_626])).
% 2.59/1.38  tff(c_649, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_635])).
% 2.59/1.38  tff(c_651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_649])).
% 2.59/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.38  
% 2.59/1.38  Inference rules
% 2.59/1.38  ----------------------
% 2.59/1.38  #Ref     : 0
% 2.59/1.38  #Sup     : 126
% 2.59/1.38  #Fact    : 0
% 2.59/1.38  #Define  : 0
% 2.59/1.38  #Split   : 5
% 2.59/1.38  #Chain   : 0
% 2.59/1.38  #Close   : 0
% 2.59/1.38  
% 2.59/1.38  Ordering : KBO
% 2.59/1.38  
% 2.59/1.38  Simplification rules
% 2.59/1.38  ----------------------
% 2.59/1.38  #Subsume      : 18
% 2.59/1.38  #Demod        : 137
% 2.59/1.38  #Tautology    : 45
% 2.59/1.38  #SimpNegUnit  : 13
% 2.59/1.38  #BackRed      : 4
% 2.59/1.38  
% 2.59/1.38  #Partial instantiations: 0
% 2.59/1.38  #Strategies tried      : 1
% 2.59/1.38  
% 2.59/1.38  Timing (in seconds)
% 2.59/1.38  ----------------------
% 2.59/1.38  Preprocessing        : 0.30
% 2.59/1.38  Parsing              : 0.16
% 2.59/1.38  CNF conversion       : 0.02
% 2.59/1.38  Main loop            : 0.31
% 2.59/1.38  Inferencing          : 0.11
% 2.59/1.38  Reduction            : 0.10
% 2.59/1.38  Demodulation         : 0.07
% 2.59/1.38  BG Simplification    : 0.02
% 2.59/1.38  Subsumption          : 0.06
% 2.59/1.38  Abstraction          : 0.02
% 2.59/1.38  MUC search           : 0.00
% 2.59/1.38  Cooper               : 0.00
% 2.59/1.38  Total                : 0.64
% 2.59/1.38  Index Insertion      : 0.00
% 2.59/1.38  Index Deletion       : 0.00
% 2.59/1.38  Index Matching       : 0.00
% 2.59/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
