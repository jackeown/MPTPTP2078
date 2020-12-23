%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:13 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   34 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 186 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_257,plain,(
    ! [A_92,B_93] :
      ( k2_pre_topc(A_92,k1_tops_1(A_92,B_93)) = B_93
      | ~ v5_tops_1(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_263,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_268,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_263])).

tff(c_34,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_269,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_34])).

tff(c_28,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k1_tops_1(A_42,B_43),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_241,plain,(
    ! [A_90,B_91] :
      ( k2_pre_topc(A_90,k2_pre_topc(A_90,B_91)) = k2_pre_topc(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_367,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,k2_pre_topc(A_109,k1_tops_1(A_109,B_110))) = k2_pre_topc(A_109,k1_tops_1(A_109,B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_28,c_241])).

tff(c_373,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_367])).

tff(c_378,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_268,c_268,c_373])).

tff(c_312,plain,(
    ! [A_104,B_105] :
      ( k4_subset_1(u1_struct_0(A_104),B_105,k2_tops_1(A_104,B_105)) = k2_pre_topc(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_318,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_312])).

tff(c_323,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_318])).

tff(c_379,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_323])).

tff(c_30,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k2_tops_1(A_44,B_45),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_210,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_558,plain,(
    ! [A_137,B_138,B_139] :
      ( k4_subset_1(u1_struct_0(A_137),B_138,k2_tops_1(A_137,B_139)) = k2_xboole_0(B_138,k2_tops_1(A_137,B_139))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_210])).

tff(c_564,plain,(
    ! [B_139] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_139)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_558])).

tff(c_570,plain,(
    ! [B_140] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_140)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_564])).

tff(c_581,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_570])).

tff(c_589,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_581])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    ! [B_58,A_59] : k3_tarski(k2_tarski(B_58,A_59)) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_84])).

tff(c_18,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    ! [A_61,B_60] : r1_tarski(A_61,k2_xboole_0(B_60,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_2])).

tff(c_594,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_137])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.68/1.38  
% 2.68/1.38  %Foreground sorts:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Background operators:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Foreground operators:
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.38  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.68/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.68/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.68/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.38  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.68/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.38  
% 2.94/1.39  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 2.94/1.39  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.94/1.39  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.94/1.39  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.94/1.39  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 2.94/1.39  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.94/1.39  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.94/1.39  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.94/1.39  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.94/1.39  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.94/1.39  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.39  tff(c_36, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.39  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.39  tff(c_257, plain, (![A_92, B_93]: (k2_pre_topc(A_92, k1_tops_1(A_92, B_93))=B_93 | ~v5_tops_1(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.94/1.39  tff(c_263, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_257])).
% 2.94/1.39  tff(c_268, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_263])).
% 2.94/1.39  tff(c_34, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.39  tff(c_269, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_34])).
% 2.94/1.39  tff(c_28, plain, (![A_42, B_43]: (m1_subset_1(k1_tops_1(A_42, B_43), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.94/1.39  tff(c_241, plain, (![A_90, B_91]: (k2_pre_topc(A_90, k2_pre_topc(A_90, B_91))=k2_pre_topc(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.39  tff(c_367, plain, (![A_109, B_110]: (k2_pre_topc(A_109, k2_pre_topc(A_109, k1_tops_1(A_109, B_110)))=k2_pre_topc(A_109, k1_tops_1(A_109, B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_28, c_241])).
% 2.94/1.39  tff(c_373, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_367])).
% 2.94/1.39  tff(c_378, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_268, c_268, c_373])).
% 2.94/1.39  tff(c_312, plain, (![A_104, B_105]: (k4_subset_1(u1_struct_0(A_104), B_105, k2_tops_1(A_104, B_105))=k2_pre_topc(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.94/1.39  tff(c_318, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_312])).
% 2.94/1.39  tff(c_323, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_318])).
% 2.94/1.39  tff(c_379, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_378, c_323])).
% 2.94/1.39  tff(c_30, plain, (![A_44, B_45]: (m1_subset_1(k2_tops_1(A_44, B_45), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.94/1.39  tff(c_210, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.39  tff(c_558, plain, (![A_137, B_138, B_139]: (k4_subset_1(u1_struct_0(A_137), B_138, k2_tops_1(A_137, B_139))=k2_xboole_0(B_138, k2_tops_1(A_137, B_139)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_30, c_210])).
% 2.94/1.39  tff(c_564, plain, (![B_139]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_139))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_558])).
% 2.94/1.39  tff(c_570, plain, (![B_140]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_140))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_564])).
% 2.94/1.39  tff(c_581, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_570])).
% 2.94/1.39  tff(c_589, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_581])).
% 2.94/1.39  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.39  tff(c_84, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.39  tff(c_99, plain, (![B_58, A_59]: (k3_tarski(k2_tarski(B_58, A_59))=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_4, c_84])).
% 2.94/1.39  tff(c_18, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.39  tff(c_122, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_99, c_18])).
% 2.94/1.39  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.39  tff(c_137, plain, (![A_61, B_60]: (r1_tarski(A_61, k2_xboole_0(B_60, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_2])).
% 2.94/1.39  tff(c_594, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_589, c_137])).
% 2.94/1.39  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_594])).
% 2.94/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.39  
% 2.94/1.39  Inference rules
% 2.94/1.39  ----------------------
% 2.94/1.39  #Ref     : 0
% 2.94/1.39  #Sup     : 136
% 2.94/1.39  #Fact    : 0
% 2.94/1.39  #Define  : 0
% 2.94/1.39  #Split   : 2
% 2.94/1.39  #Chain   : 0
% 2.94/1.39  #Close   : 0
% 2.94/1.39  
% 2.94/1.39  Ordering : KBO
% 2.94/1.39  
% 2.94/1.39  Simplification rules
% 2.94/1.39  ----------------------
% 2.94/1.39  #Subsume      : 3
% 2.94/1.39  #Demod        : 38
% 2.94/1.39  #Tautology    : 83
% 2.94/1.39  #SimpNegUnit  : 1
% 2.94/1.39  #BackRed      : 3
% 2.94/1.39  
% 2.94/1.39  #Partial instantiations: 0
% 2.94/1.39  #Strategies tried      : 1
% 2.94/1.39  
% 2.94/1.39  Timing (in seconds)
% 2.94/1.39  ----------------------
% 2.94/1.40  Preprocessing        : 0.34
% 2.94/1.40  Parsing              : 0.19
% 2.94/1.40  CNF conversion       : 0.02
% 2.94/1.40  Main loop            : 0.33
% 2.94/1.40  Inferencing          : 0.13
% 2.94/1.40  Reduction            : 0.11
% 2.94/1.40  Demodulation         : 0.08
% 2.94/1.40  BG Simplification    : 0.02
% 2.94/1.40  Subsumption          : 0.06
% 2.94/1.40  Abstraction          : 0.02
% 2.94/1.40  MUC search           : 0.00
% 2.94/1.40  Cooper               : 0.00
% 2.94/1.40  Total                : 0.71
% 2.94/1.40  Index Insertion      : 0.00
% 2.94/1.40  Index Deletion       : 0.00
% 2.94/1.40  Index Matching       : 0.00
% 2.94/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
