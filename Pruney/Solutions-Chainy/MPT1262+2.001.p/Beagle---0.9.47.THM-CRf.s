%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:36 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 169 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 380 expanded)
%              Number of equality atoms :   25 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_22,plain,(
    ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_85,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_28])).

tff(c_244,plain,(
    ! [B_44,A_45] :
      ( v1_tops_1(B_44,A_45)
      | k2_pre_topc(A_45,B_44) != k2_struct_0(A_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_254,plain,(
    ! [B_44] :
      ( v1_tops_1(B_44,'#skF_1')
      | k2_pre_topc('#skF_1',B_44) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_244])).

tff(c_259,plain,(
    ! [B_46] :
      ( v1_tops_1(B_46,'#skF_1')
      | k2_pre_topc('#skF_1',B_46) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_254])).

tff(c_268,plain,
    ( v1_tops_1('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_259])).

tff(c_278,plain,(
    k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_268])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k2_pre_topc(A_36,B_37),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_37] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_37),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_145])).

tff(c_163,plain,(
    ! [B_38] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_38),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_85,c_151])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [B_39] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_39),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_163,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [B_39] :
      ( k2_xboole_0(k2_pre_topc('#skF_1',B_39),k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_185,plain,(
    ! [B_42] :
      ( k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_42)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_201,plain,(
    k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_185])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_89,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_30])).

tff(c_26,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_322,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,B_52) = k2_struct_0(A_51)
      | ~ v1_tops_1(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_332,plain,(
    ! [B_52] :
      ( k2_pre_topc('#skF_1',B_52) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_322])).

tff(c_337,plain,(
    ! [B_53] :
      ( k2_pre_topc('#skF_1',B_53) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_53,'#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_332])).

tff(c_343,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_337])).

tff(c_354,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_343])).

tff(c_401,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(k2_pre_topc(A_54,B_55),k2_pre_topc(A_54,C_56))
      | ~ r1_tarski(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_407,plain,(
    ! [C_56] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_56))
      | ~ r1_tarski('#skF_2',C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_401])).

tff(c_789,plain,(
    ! [C_80] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_80))
      | ~ r1_tarski('#skF_2',C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_89,c_85,c_85,c_407])).

tff(c_989,plain,(
    ! [C_94] :
      ( k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_94)) = k2_pre_topc('#skF_1',C_94)
      | ~ r1_tarski('#skF_2',C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_789,c_4])).

tff(c_1001,plain,
    ( k2_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3')) = k2_pre_topc('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_989])).

tff(c_1014,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_201,c_1001])).

tff(c_1016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_1014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:23:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.46  
% 3.17/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.46  %$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.46  
% 3.17/1.46  %Foreground sorts:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Background operators:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Foreground operators:
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.17/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.46  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.17/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.17/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.17/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.46  
% 3.17/1.47  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 3.17/1.47  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.17/1.47  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.17/1.47  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.17/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.17/1.47  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.17/1.47  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.47  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.17/1.47  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.17/1.47  tff(c_22, plain, (~v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.47  tff(c_34, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.47  tff(c_81, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_14, c_34])).
% 3.17/1.47  tff(c_85, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_81])).
% 3.17/1.47  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_28])).
% 3.17/1.47  tff(c_244, plain, (![B_44, A_45]: (v1_tops_1(B_44, A_45) | k2_pre_topc(A_45, B_44)!=k2_struct_0(A_45) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.47  tff(c_254, plain, (![B_44]: (v1_tops_1(B_44, '#skF_1') | k2_pre_topc('#skF_1', B_44)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_44, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_244])).
% 3.17/1.47  tff(c_259, plain, (![B_46]: (v1_tops_1(B_46, '#skF_1') | k2_pre_topc('#skF_1', B_46)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_254])).
% 3.17/1.47  tff(c_268, plain, (v1_tops_1('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_259])).
% 3.17/1.47  tff(c_278, plain, (k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_22, c_268])).
% 3.17/1.47  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.17/1.47  tff(c_145, plain, (![A_36, B_37]: (m1_subset_1(k2_pre_topc(A_36, B_37), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.17/1.47  tff(c_151, plain, (![B_37]: (m1_subset_1(k2_pre_topc('#skF_1', B_37), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_145])).
% 3.17/1.47  tff(c_163, plain, (![B_38]: (m1_subset_1(k2_pre_topc('#skF_1', B_38), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_38, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_85, c_151])).
% 3.17/1.47  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.47  tff(c_168, plain, (![B_39]: (r1_tarski(k2_pre_topc('#skF_1', B_39), k2_struct_0('#skF_1')) | ~m1_subset_1(B_39, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_163, c_6])).
% 3.17/1.47  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.47  tff(c_171, plain, (![B_39]: (k2_xboole_0(k2_pre_topc('#skF_1', B_39), k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(B_39, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_168, c_4])).
% 3.17/1.47  tff(c_185, plain, (![B_42]: (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_42))=k2_struct_0('#skF_1') | ~m1_subset_1(B_42, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_171])).
% 3.17/1.47  tff(c_201, plain, (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_185])).
% 3.17/1.47  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_89, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_30])).
% 3.17/1.47  tff(c_26, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_322, plain, (![A_51, B_52]: (k2_pre_topc(A_51, B_52)=k2_struct_0(A_51) | ~v1_tops_1(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.47  tff(c_332, plain, (![B_52]: (k2_pre_topc('#skF_1', B_52)=k2_struct_0('#skF_1') | ~v1_tops_1(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_322])).
% 3.17/1.47  tff(c_337, plain, (![B_53]: (k2_pre_topc('#skF_1', B_53)=k2_struct_0('#skF_1') | ~v1_tops_1(B_53, '#skF_1') | ~m1_subset_1(B_53, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_332])).
% 3.17/1.47  tff(c_343, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_89, c_337])).
% 3.17/1.47  tff(c_354, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_343])).
% 3.17/1.47  tff(c_401, plain, (![A_54, B_55, C_56]: (r1_tarski(k2_pre_topc(A_54, B_55), k2_pre_topc(A_54, C_56)) | ~r1_tarski(B_55, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.17/1.47  tff(c_407, plain, (![C_56]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_56)) | ~r1_tarski('#skF_2', C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_354, c_401])).
% 3.17/1.47  tff(c_789, plain, (![C_80]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_80)) | ~r1_tarski('#skF_2', C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_89, c_85, c_85, c_407])).
% 3.17/1.47  tff(c_989, plain, (![C_94]: (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_94))=k2_pre_topc('#skF_1', C_94) | ~r1_tarski('#skF_2', C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_789, c_4])).
% 3.17/1.47  tff(c_1001, plain, (k2_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'))=k2_pre_topc('#skF_1', '#skF_3') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_989])).
% 3.17/1.47  tff(c_1014, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_201, c_1001])).
% 3.17/1.47  tff(c_1016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_1014])).
% 3.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  Inference rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Ref     : 0
% 3.17/1.47  #Sup     : 208
% 3.17/1.47  #Fact    : 0
% 3.17/1.47  #Define  : 0
% 3.17/1.48  #Split   : 4
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 32
% 3.17/1.48  #Demod        : 243
% 3.17/1.48  #Tautology    : 109
% 3.17/1.48  #SimpNegUnit  : 19
% 3.17/1.48  #BackRed      : 6
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.48  Preprocessing        : 0.31
% 3.17/1.48  Parsing              : 0.17
% 3.17/1.48  CNF conversion       : 0.02
% 3.17/1.48  Main loop            : 0.41
% 3.17/1.48  Inferencing          : 0.15
% 3.17/1.48  Reduction            : 0.13
% 3.17/1.48  Demodulation         : 0.10
% 3.17/1.48  BG Simplification    : 0.02
% 3.17/1.48  Subsumption          : 0.07
% 3.17/1.48  Abstraction          : 0.02
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.48  Cooper               : 0.00
% 3.17/1.48  Total                : 0.75
% 3.17/1.48  Index Insertion      : 0.00
% 3.17/1.48  Index Deletion       : 0.00
% 3.17/1.48  Index Matching       : 0.00
% 3.17/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
