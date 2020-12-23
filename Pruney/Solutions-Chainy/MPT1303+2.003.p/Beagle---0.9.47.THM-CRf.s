%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:47 EST 2020

% Result     : Theorem 46.23s
% Output     : CNFRefutation 46.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 172 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 329 expanded)
%              Number of equality atoms :   16 (  68 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [B_49,B_50,A_51] :
      ( k9_subset_1(B_49,B_50,A_51) = k3_xboole_0(B_50,A_51)
      | ~ r1_tarski(A_51,B_49) ) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_143,plain,(
    ! [B_2,B_50] : k9_subset_1(B_2,B_50,B_2) = k3_xboole_0(B_50,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_297,plain,(
    ! [A_72,C_73,B_74] :
      ( k9_subset_1(A_72,C_73,B_74) = k9_subset_1(A_72,B_74,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_612,plain,(
    ! [B_84,B_85,A_86] :
      ( k9_subset_1(B_84,B_85,A_86) = k9_subset_1(B_84,A_86,B_85)
      | ~ r1_tarski(A_86,B_84) ) ),
    inference(resolution,[status(thm)],[c_20,c_297])).

tff(c_636,plain,(
    ! [B_2,B_85] : k9_subset_1(B_2,B_85,B_2) = k9_subset_1(B_2,B_2,B_85) ),
    inference(resolution,[status(thm)],[c_6,c_612])).

tff(c_653,plain,(
    ! [B_87,B_88] : k9_subset_1(B_87,B_87,B_88) = k3_xboole_0(B_88,B_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_636])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,(
    ! [B_45] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_45,'#skF_2') = k3_xboole_0(B_45,'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_670,plain,(
    k3_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2') = k3_xboole_0('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_104])).

tff(c_153,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k9_subset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_236,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k9_subset_1(A_63,B_64,C_65),A_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_247,plain,(
    ! [B_50,B_2] :
      ( r1_tarski(k3_xboole_0(B_50,B_2),B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_236])).

tff(c_760,plain,
    ( r1_tarski(k3_xboole_0('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_247])).

tff(c_2993,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_2996,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_2993])).

tff(c_3000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2996])).

tff(c_3002,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_164,plain,(
    ! [B_45] :
      ( m1_subset_1(k3_xboole_0(B_45,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_153])).

tff(c_171,plain,(
    ! [B_45] : m1_subset_1(k3_xboole_0(B_45,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_164])).

tff(c_169,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(k9_subset_1(A_54,B_55,C_56),A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_464,plain,(
    ! [B_77,A_78,C_79] :
      ( v1_tops_2(B_77,A_78)
      | ~ v1_tops_2(C_79,A_78)
      | ~ r1_tarski(B_77,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4486,plain,(
    ! [A_201,B_202,C_203,A_204] :
      ( v1_tops_2(k9_subset_1(A_201,B_202,C_203),A_204)
      | ~ v1_tops_2(A_201,A_204)
      | ~ m1_subset_1(A_201,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204))))
      | ~ m1_subset_1(k9_subset_1(A_201,B_202,C_203),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204))))
      | ~ l1_pre_topc(A_204)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_201)) ) ),
    inference(resolution,[status(thm)],[c_169,c_464])).

tff(c_4538,plain,(
    ! [B_2,B_50,A_204] :
      ( v1_tops_2(k9_subset_1(B_2,B_50,B_2),A_204)
      | ~ v1_tops_2(B_2,A_204)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204))))
      | ~ m1_subset_1(k3_xboole_0(B_50,B_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204))))
      | ~ l1_pre_topc(A_204)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_4486])).

tff(c_105813,plain,(
    ! [B_1342,B_1343,A_1344] :
      ( v1_tops_2(k3_xboole_0(B_1342,B_1343),A_1344)
      | ~ v1_tops_2(B_1343,A_1344)
      | ~ m1_subset_1(B_1343,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1344))))
      | ~ m1_subset_1(k3_xboole_0(B_1342,B_1343),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1344))))
      | ~ l1_pre_topc(A_1344)
      | ~ m1_subset_1(B_1343,k1_zfmisc_1(B_1343)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_4538])).

tff(c_105957,plain,(
    ! [B_45] :
      ( v1_tops_2(k3_xboole_0(B_45,'#skF_2'),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_171,c_105813])).

tff(c_106054,plain,(
    ! [B_45] : v1_tops_2(k3_xboole_0(B_45,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_32,c_30,c_26,c_105957])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_103,plain,(
    ! [B_45] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_45,'#skF_3') = k3_xboole_0(B_45,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_309,plain,(
    ! [B_74] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_74,'#skF_3') = k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3',B_74) ),
    inference(resolution,[status(thm)],[c_28,c_297])).

tff(c_321,plain,(
    ! [B_75] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3',B_75) = k3_xboole_0(B_75,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_309])).

tff(c_338,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_104])).

tff(c_24,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_105,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_24])).

tff(c_364,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_105])).

tff(c_106058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106054,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 46.23/35.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.23/35.72  
% 46.23/35.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.23/35.72  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 46.23/35.72  
% 46.23/35.72  %Foreground sorts:
% 46.23/35.72  
% 46.23/35.72  
% 46.23/35.72  %Background operators:
% 46.23/35.72  
% 46.23/35.72  
% 46.23/35.72  %Foreground operators:
% 46.23/35.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 46.23/35.72  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 46.23/35.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 46.23/35.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 46.23/35.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 46.23/35.72  tff('#skF_2', type, '#skF_2': $i).
% 46.23/35.72  tff('#skF_3', type, '#skF_3': $i).
% 46.23/35.72  tff('#skF_1', type, '#skF_1': $i).
% 46.23/35.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 46.23/35.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 46.23/35.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 46.23/35.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 46.23/35.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 46.23/35.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 46.23/35.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 46.23/35.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 46.23/35.72  
% 46.23/35.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 46.23/35.73  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 46.23/35.73  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 46.23/35.73  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 46.23/35.73  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 46.23/35.73  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 46.23/35.73  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 46.23/35.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 46.23/35.73  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 46.23/35.73  tff(c_95, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 46.23/35.73  tff(c_126, plain, (![B_49, B_50, A_51]: (k9_subset_1(B_49, B_50, A_51)=k3_xboole_0(B_50, A_51) | ~r1_tarski(A_51, B_49))), inference(resolution, [status(thm)], [c_20, c_95])).
% 46.23/35.73  tff(c_143, plain, (![B_2, B_50]: (k9_subset_1(B_2, B_50, B_2)=k3_xboole_0(B_50, B_2))), inference(resolution, [status(thm)], [c_6, c_126])).
% 46.23/35.73  tff(c_297, plain, (![A_72, C_73, B_74]: (k9_subset_1(A_72, C_73, B_74)=k9_subset_1(A_72, B_74, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 46.23/35.73  tff(c_612, plain, (![B_84, B_85, A_86]: (k9_subset_1(B_84, B_85, A_86)=k9_subset_1(B_84, A_86, B_85) | ~r1_tarski(A_86, B_84))), inference(resolution, [status(thm)], [c_20, c_297])).
% 46.23/35.73  tff(c_636, plain, (![B_2, B_85]: (k9_subset_1(B_2, B_85, B_2)=k9_subset_1(B_2, B_2, B_85))), inference(resolution, [status(thm)], [c_6, c_612])).
% 46.23/35.73  tff(c_653, plain, (![B_87, B_88]: (k9_subset_1(B_87, B_87, B_88)=k3_xboole_0(B_88, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_636])).
% 46.23/35.73  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 46.23/35.73  tff(c_104, plain, (![B_45]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_45, '#skF_2')=k3_xboole_0(B_45, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_95])).
% 46.23/35.73  tff(c_670, plain, (k3_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2')=k3_xboole_0('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_653, c_104])).
% 46.23/35.73  tff(c_153, plain, (![A_54, B_55, C_56]: (m1_subset_1(k9_subset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 46.23/35.73  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 46.23/35.73  tff(c_236, plain, (![A_63, B_64, C_65]: (r1_tarski(k9_subset_1(A_63, B_64, C_65), A_63) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_153, c_18])).
% 46.23/35.73  tff(c_247, plain, (![B_50, B_2]: (r1_tarski(k3_xboole_0(B_50, B_2), B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_236])).
% 46.23/35.73  tff(c_760, plain, (r1_tarski(k3_xboole_0('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_670, c_247])).
% 46.23/35.73  tff(c_2993, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_760])).
% 46.23/35.73  tff(c_2996, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_2993])).
% 46.23/35.73  tff(c_3000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2996])).
% 46.23/35.73  tff(c_3002, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_760])).
% 46.23/35.73  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 46.23/35.73  tff(c_26, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 46.23/35.73  tff(c_164, plain, (![B_45]: (m1_subset_1(k3_xboole_0(B_45, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_153])).
% 46.23/35.73  tff(c_171, plain, (![B_45]: (m1_subset_1(k3_xboole_0(B_45, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_164])).
% 46.23/35.73  tff(c_169, plain, (![A_54, B_55, C_56]: (r1_tarski(k9_subset_1(A_54, B_55, C_56), A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_153, c_18])).
% 46.23/35.73  tff(c_464, plain, (![B_77, A_78, C_79]: (v1_tops_2(B_77, A_78) | ~v1_tops_2(C_79, A_78) | ~r1_tarski(B_77, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 46.23/35.73  tff(c_4486, plain, (![A_201, B_202, C_203, A_204]: (v1_tops_2(k9_subset_1(A_201, B_202, C_203), A_204) | ~v1_tops_2(A_201, A_204) | ~m1_subset_1(A_201, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204)))) | ~m1_subset_1(k9_subset_1(A_201, B_202, C_203), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204)))) | ~l1_pre_topc(A_204) | ~m1_subset_1(C_203, k1_zfmisc_1(A_201)))), inference(resolution, [status(thm)], [c_169, c_464])).
% 46.23/35.73  tff(c_4538, plain, (![B_2, B_50, A_204]: (v1_tops_2(k9_subset_1(B_2, B_50, B_2), A_204) | ~v1_tops_2(B_2, A_204) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204)))) | ~m1_subset_1(k3_xboole_0(B_50, B_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_204)))) | ~l1_pre_topc(A_204) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_4486])).
% 46.23/35.73  tff(c_105813, plain, (![B_1342, B_1343, A_1344]: (v1_tops_2(k3_xboole_0(B_1342, B_1343), A_1344) | ~v1_tops_2(B_1343, A_1344) | ~m1_subset_1(B_1343, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1344)))) | ~m1_subset_1(k3_xboole_0(B_1342, B_1343), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1344)))) | ~l1_pre_topc(A_1344) | ~m1_subset_1(B_1343, k1_zfmisc_1(B_1343)))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_4538])).
% 46.23/35.73  tff(c_105957, plain, (![B_45]: (v1_tops_2(k3_xboole_0(B_45, '#skF_2'), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_171, c_105813])).
% 46.23/35.73  tff(c_106054, plain, (![B_45]: (v1_tops_2(k3_xboole_0(B_45, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_32, c_30, c_26, c_105957])).
% 46.23/35.73  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 46.23/35.73  tff(c_103, plain, (![B_45]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_45, '#skF_3')=k3_xboole_0(B_45, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_95])).
% 46.23/35.73  tff(c_309, plain, (![B_74]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_74, '#skF_3')=k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3', B_74))), inference(resolution, [status(thm)], [c_28, c_297])).
% 46.23/35.73  tff(c_321, plain, (![B_75]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3', B_75)=k3_xboole_0(B_75, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_309])).
% 46.23/35.73  tff(c_338, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_321, c_104])).
% 46.23/35.73  tff(c_24, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 46.23/35.73  tff(c_105, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_24])).
% 46.23/35.73  tff(c_364, plain, (~v1_tops_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_105])).
% 46.23/35.73  tff(c_106058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106054, c_364])).
% 46.23/35.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.23/35.73  
% 46.23/35.73  Inference rules
% 46.23/35.73  ----------------------
% 46.23/35.73  #Ref     : 0
% 46.23/35.73  #Sup     : 27197
% 46.23/35.73  #Fact    : 0
% 46.23/35.73  #Define  : 0
% 46.23/35.73  #Split   : 10
% 46.23/35.73  #Chain   : 0
% 46.23/35.73  #Close   : 0
% 46.23/35.73  
% 46.23/35.73  Ordering : KBO
% 46.23/35.73  
% 46.23/35.73  Simplification rules
% 46.23/35.73  ----------------------
% 46.23/35.73  #Subsume      : 2390
% 46.23/35.73  #Demod        : 12433
% 46.23/35.73  #Tautology    : 5248
% 46.23/35.73  #SimpNegUnit  : 0
% 46.23/35.73  #BackRed      : 10
% 46.23/35.73  
% 46.23/35.73  #Partial instantiations: 0
% 46.23/35.73  #Strategies tried      : 1
% 46.23/35.73  
% 46.23/35.73  Timing (in seconds)
% 46.23/35.73  ----------------------
% 46.23/35.74  Preprocessing        : 0.33
% 46.23/35.74  Parsing              : 0.17
% 46.23/35.74  CNF conversion       : 0.02
% 46.23/35.74  Main loop            : 34.58
% 46.23/35.74  Inferencing          : 3.72
% 46.23/35.74  Reduction            : 18.90
% 46.23/35.74  Demodulation         : 17.29
% 46.23/35.74  BG Simplification    : 0.61
% 46.23/35.74  Subsumption          : 9.57
% 46.23/35.74  Abstraction          : 0.81
% 46.23/35.74  MUC search           : 0.00
% 46.23/35.74  Cooper               : 0.00
% 46.23/35.74  Total                : 34.94
% 46.23/35.74  Index Insertion      : 0.00
% 46.23/35.74  Index Deletion       : 0.00
% 46.23/35.74  Index Matching       : 0.00
% 46.23/35.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
