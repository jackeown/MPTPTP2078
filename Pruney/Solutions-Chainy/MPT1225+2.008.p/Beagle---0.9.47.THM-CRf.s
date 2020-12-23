%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:28 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 114 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 293 expanded)
%              Number of equality atoms :   19 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_75,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_50,axiom,(
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

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_37,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_150,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,B_51) = B_51
      | ~ v4_pre_topc(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_160,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_167,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_160])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,C_40) = k3_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [B_39] : k9_subset_1(u1_struct_0('#skF_1'),B_39,'#skF_3') = k3_xboole_0(B_39,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_26,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_157,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_164,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_157])).

tff(c_24,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_24])).

tff(c_181,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_78,c_164,c_80])).

tff(c_277,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_pre_topc(A_66,k9_subset_1(u1_struct_0(A_66),B_67,C_68)),k9_subset_1(u1_struct_0(A_66),k2_pre_topc(A_66,B_67),k2_pre_topc(A_66,C_68)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_307,plain,(
    ! [B_39] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_39,'#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_39),k2_pre_topc('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_277])).

tff(c_482,plain,(
    ! [B_83] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_83,'#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1',B_83),'#skF_3'))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_78,c_164,c_307])).

tff(c_492,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_482])).

tff(c_500,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_492])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,k2_pre_topc(A_49,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_187,plain,(
    ! [A_52,A_53] :
      ( r1_tarski(A_52,k2_pre_topc(A_53,A_52))
      | ~ l1_pre_topc(A_53)
      | ~ r1_tarski(A_52,u1_struct_0(A_53)) ) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [A_53,A_52] :
      ( k2_pre_topc(A_53,A_52) = A_52
      | ~ r1_tarski(k2_pre_topc(A_53,A_52),A_52)
      | ~ l1_pre_topc(A_53)
      | ~ r1_tarski(A_52,u1_struct_0(A_53)) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_505,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_500,c_199])).

tff(c_515,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_505])).

tff(c_516,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_515])).

tff(c_526,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_516])).

tff(c_530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.39  
% 2.57/1.39  %Foreground sorts:
% 2.57/1.39  
% 2.57/1.39  
% 2.57/1.39  %Background operators:
% 2.57/1.39  
% 2.57/1.39  
% 2.57/1.39  %Foreground operators:
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.57/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.57/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.39  
% 2.57/1.40  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_1)).
% 2.57/1.40  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.57/1.40  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.57/1.40  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.57/1.40  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.57/1.40  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 2.57/1.40  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.57/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.40  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.40  tff(c_37, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.40  tff(c_45, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_37])).
% 2.57/1.40  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.40  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.40  tff(c_28, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.40  tff(c_150, plain, (![A_50, B_51]: (k2_pre_topc(A_50, B_51)=B_51 | ~v4_pre_topc(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.40  tff(c_160, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_150])).
% 2.57/1.40  tff(c_167, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_160])).
% 2.57/1.40  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.40  tff(c_70, plain, (![A_38, B_39, C_40]: (k9_subset_1(A_38, B_39, C_40)=k3_xboole_0(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.40  tff(c_78, plain, (![B_39]: (k9_subset_1(u1_struct_0('#skF_1'), B_39, '#skF_3')=k3_xboole_0(B_39, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_70])).
% 2.57/1.40  tff(c_26, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.40  tff(c_157, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_150])).
% 2.57/1.40  tff(c_164, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_157])).
% 2.57/1.40  tff(c_24, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.40  tff(c_80, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_24])).
% 2.57/1.40  tff(c_181, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_78, c_164, c_80])).
% 2.57/1.40  tff(c_277, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_pre_topc(A_66, k9_subset_1(u1_struct_0(A_66), B_67, C_68)), k9_subset_1(u1_struct_0(A_66), k2_pre_topc(A_66, B_67), k2_pre_topc(A_66, C_68))) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.57/1.40  tff(c_307, plain, (![B_39]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_39, '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_39), k2_pre_topc('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_277])).
% 2.57/1.40  tff(c_482, plain, (![B_83]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_83, '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', B_83), '#skF_3')) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_78, c_164, c_307])).
% 2.57/1.40  tff(c_492, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_482])).
% 2.57/1.40  tff(c_500, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_492])).
% 2.57/1.40  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.40  tff(c_123, plain, (![B_48, A_49]: (r1_tarski(B_48, k2_pre_topc(A_49, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.57/1.40  tff(c_187, plain, (![A_52, A_53]: (r1_tarski(A_52, k2_pre_topc(A_53, A_52)) | ~l1_pre_topc(A_53) | ~r1_tarski(A_52, u1_struct_0(A_53)))), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.57/1.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.40  tff(c_199, plain, (![A_53, A_52]: (k2_pre_topc(A_53, A_52)=A_52 | ~r1_tarski(k2_pre_topc(A_53, A_52), A_52) | ~l1_pre_topc(A_53) | ~r1_tarski(A_52, u1_struct_0(A_53)))), inference(resolution, [status(thm)], [c_187, c_2])).
% 2.57/1.40  tff(c_505, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_500, c_199])).
% 2.57/1.40  tff(c_515, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_505])).
% 2.57/1.40  tff(c_516, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_181, c_515])).
% 2.57/1.40  tff(c_526, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_516])).
% 2.57/1.40  tff(c_530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_526])).
% 2.57/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.40  
% 2.57/1.40  Inference rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Ref     : 0
% 2.57/1.40  #Sup     : 105
% 2.57/1.40  #Fact    : 0
% 2.57/1.40  #Define  : 0
% 2.57/1.40  #Split   : 2
% 2.57/1.40  #Chain   : 0
% 2.57/1.40  #Close   : 0
% 2.57/1.40  
% 2.57/1.40  Ordering : KBO
% 2.57/1.40  
% 2.57/1.40  Simplification rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Subsume      : 0
% 2.57/1.40  #Demod        : 129
% 2.57/1.40  #Tautology    : 41
% 2.57/1.40  #SimpNegUnit  : 3
% 2.57/1.40  #BackRed      : 3
% 2.57/1.40  
% 2.57/1.40  #Partial instantiations: 0
% 2.57/1.40  #Strategies tried      : 1
% 2.57/1.40  
% 2.57/1.40  Timing (in seconds)
% 2.57/1.40  ----------------------
% 2.57/1.41  Preprocessing        : 0.30
% 2.57/1.41  Parsing              : 0.15
% 2.57/1.41  CNF conversion       : 0.02
% 2.57/1.41  Main loop            : 0.30
% 2.57/1.41  Inferencing          : 0.10
% 2.57/1.41  Reduction            : 0.10
% 2.57/1.41  Demodulation         : 0.08
% 2.57/1.41  BG Simplification    : 0.02
% 2.57/1.41  Subsumption          : 0.06
% 2.57/1.41  Abstraction          : 0.02
% 2.57/1.41  MUC search           : 0.00
% 2.57/1.41  Cooper               : 0.00
% 2.57/1.41  Total                : 0.63
% 2.57/1.41  Index Insertion      : 0.00
% 2.57/1.41  Index Deletion       : 0.00
% 2.57/1.41  Index Matching       : 0.00
% 2.57/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
