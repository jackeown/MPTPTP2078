%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:19 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 123 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 248 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_165,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_173,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_165])).

tff(c_178,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_173])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_317,plain,(
    ! [A_71,B_72] :
      ( k2_pre_topc(A_71,k1_tops_1(A_71,B_72)) = B_72
      | ~ v5_tops_1(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_325,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_317])).

tff(c_330,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_325])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_331,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_24])).

tff(c_69,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [B_12,A_11] :
      ( k4_xboole_0(B_12,A_11) = k3_subset_1(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_189,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_178,c_80])).

tff(c_100,plain,(
    ! [A_43,B_44,C_45] :
      ( k7_subset_1(A_43,B_44,C_45) = k4_xboole_0(B_44,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [C_45] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_45) = k4_xboole_0('#skF_2',C_45) ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_41,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_29] :
      ( r1_tarski(A_29,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_29,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_41])).

tff(c_199,plain,(
    ! [A_56,B_57] :
      ( k2_pre_topc(A_56,k2_pre_topc(A_56,B_57)) = k2_pre_topc(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_336,plain,(
    ! [A_73,A_74] :
      ( k2_pre_topc(A_73,k2_pre_topc(A_73,A_74)) = k2_pre_topc(A_73,A_74)
      | ~ l1_pre_topc(A_73)
      | ~ r1_tarski(A_74,u1_struct_0(A_73)) ) ),
    inference(resolution,[status(thm)],[c_12,c_199])).

tff(c_346,plain,(
    ! [A_29] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_29)) = k2_pre_topc('#skF_1',A_29)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_29,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_336])).

tff(c_384,plain,(
    ! [A_75] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',A_75)) = k2_pre_topc('#skF_1',A_75)
      | ~ r1_tarski(A_75,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_346])).

tff(c_402,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_384])).

tff(c_414,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_330,c_402])).

tff(c_643,plain,(
    ! [A_97,B_98] :
      ( k7_subset_1(u1_struct_0(A_97),k2_pre_topc(A_97,B_98),k1_tops_1(A_97,B_98)) = k2_tops_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_659,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_643])).

tff(c_677,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_189,c_109,c_659])).

tff(c_57,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k3_subset_1(A_35,B_36),A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_57,c_10])).

tff(c_700,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_61])).

tff(c_710,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_700])).

tff(c_714,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_710])).

tff(c_718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:09:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.53  
% 2.93/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.54  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.93/1.54  
% 2.93/1.54  %Foreground sorts:
% 2.93/1.54  
% 2.93/1.54  
% 2.93/1.54  %Background operators:
% 2.93/1.54  
% 2.93/1.54  
% 2.93/1.54  %Foreground operators:
% 2.93/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.54  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.93/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.93/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.93/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.93/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.54  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.93/1.54  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.54  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.93/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.93/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.54  
% 2.93/1.55  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 2.93/1.55  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.93/1.55  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.93/1.55  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.93/1.55  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.93/1.55  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.93/1.55  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.93/1.55  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.93/1.55  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.93/1.55  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.93/1.55  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.93/1.55  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.93/1.55  tff(c_165, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.93/1.55  tff(c_173, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_165])).
% 2.93/1.55  tff(c_178, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_173])).
% 2.93/1.55  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.55  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.93/1.55  tff(c_317, plain, (![A_71, B_72]: (k2_pre_topc(A_71, k1_tops_1(A_71, B_72))=B_72 | ~v5_tops_1(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.55  tff(c_325, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_317])).
% 2.93/1.55  tff(c_330, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_325])).
% 2.93/1.55  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.93/1.55  tff(c_331, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_24])).
% 2.93/1.55  tff(c_69, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.55  tff(c_80, plain, (![B_12, A_11]: (k4_xboole_0(B_12, A_11)=k3_subset_1(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_12, c_69])).
% 2.93/1.55  tff(c_189, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_178, c_80])).
% 2.93/1.55  tff(c_100, plain, (![A_43, B_44, C_45]: (k7_subset_1(A_43, B_44, C_45)=k4_xboole_0(B_44, C_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.55  tff(c_109, plain, (![C_45]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_45)=k4_xboole_0('#skF_2', C_45))), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.93/1.55  tff(c_32, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.55  tff(c_40, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.93/1.55  tff(c_41, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.55  tff(c_44, plain, (![A_29]: (r1_tarski(A_29, u1_struct_0('#skF_1')) | ~r1_tarski(A_29, '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_41])).
% 2.93/1.55  tff(c_199, plain, (![A_56, B_57]: (k2_pre_topc(A_56, k2_pre_topc(A_56, B_57))=k2_pre_topc(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.93/1.55  tff(c_336, plain, (![A_73, A_74]: (k2_pre_topc(A_73, k2_pre_topc(A_73, A_74))=k2_pre_topc(A_73, A_74) | ~l1_pre_topc(A_73) | ~r1_tarski(A_74, u1_struct_0(A_73)))), inference(resolution, [status(thm)], [c_12, c_199])).
% 2.93/1.55  tff(c_346, plain, (![A_29]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_29))=k2_pre_topc('#skF_1', A_29) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_29, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_336])).
% 2.93/1.55  tff(c_384, plain, (![A_75]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', A_75))=k2_pre_topc('#skF_1', A_75) | ~r1_tarski(A_75, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_346])).
% 2.93/1.55  tff(c_402, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_330, c_384])).
% 2.93/1.55  tff(c_414, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_330, c_402])).
% 2.93/1.55  tff(c_643, plain, (![A_97, B_98]: (k7_subset_1(u1_struct_0(A_97), k2_pre_topc(A_97, B_98), k1_tops_1(A_97, B_98))=k2_tops_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.93/1.55  tff(c_659, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_414, c_643])).
% 2.93/1.55  tff(c_677, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_189, c_109, c_659])).
% 2.93/1.55  tff(c_57, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.55  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.55  tff(c_61, plain, (![A_35, B_36]: (r1_tarski(k3_subset_1(A_35, B_36), A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(resolution, [status(thm)], [c_57, c_10])).
% 2.93/1.55  tff(c_700, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_677, c_61])).
% 2.93/1.55  tff(c_710, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_331, c_700])).
% 2.93/1.55  tff(c_714, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_12, c_710])).
% 2.93/1.55  tff(c_718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_714])).
% 2.93/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.55  
% 2.93/1.55  Inference rules
% 2.93/1.55  ----------------------
% 2.93/1.55  #Ref     : 0
% 2.93/1.55  #Sup     : 165
% 2.93/1.55  #Fact    : 0
% 2.93/1.55  #Define  : 0
% 2.93/1.55  #Split   : 1
% 2.93/1.55  #Chain   : 0
% 2.93/1.55  #Close   : 0
% 2.93/1.55  
% 2.93/1.55  Ordering : KBO
% 2.93/1.55  
% 2.93/1.55  Simplification rules
% 2.93/1.55  ----------------------
% 2.93/1.55  #Subsume      : 15
% 2.93/1.55  #Demod        : 57
% 2.93/1.55  #Tautology    : 67
% 2.93/1.55  #SimpNegUnit  : 1
% 2.93/1.55  #BackRed      : 2
% 2.93/1.55  
% 2.93/1.55  #Partial instantiations: 0
% 2.93/1.55  #Strategies tried      : 1
% 2.93/1.55  
% 2.93/1.55  Timing (in seconds)
% 2.93/1.55  ----------------------
% 2.93/1.55  Preprocessing        : 0.37
% 2.93/1.55  Parsing              : 0.19
% 2.93/1.55  CNF conversion       : 0.02
% 2.93/1.55  Main loop            : 0.34
% 2.93/1.55  Inferencing          : 0.13
% 2.93/1.55  Reduction            : 0.10
% 2.93/1.55  Demodulation         : 0.07
% 2.93/1.55  BG Simplification    : 0.02
% 2.93/1.55  Subsumption          : 0.07
% 2.93/1.55  Abstraction          : 0.02
% 2.93/1.55  MUC search           : 0.00
% 2.93/1.55  Cooper               : 0.00
% 2.93/1.55  Total                : 0.75
% 2.93/1.55  Index Insertion      : 0.00
% 2.93/1.55  Index Deletion       : 0.00
% 2.93/1.55  Index Matching       : 0.00
% 2.93/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
