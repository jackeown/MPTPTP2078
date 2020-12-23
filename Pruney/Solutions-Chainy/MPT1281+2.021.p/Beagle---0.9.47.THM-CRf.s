%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:16 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 110 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 210 expanded)
%              Number of equality atoms :   27 (  35 expanded)
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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_177,plain,(
    ! [A_89,B_90] :
      ( k2_pre_topc(A_89,k1_tops_1(A_89,B_90)) = B_90
      | ~ v5_tops_1(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_183,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_188,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_183])).

tff(c_34,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_189,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_34])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k1_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_98,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,k2_pre_topc(A_79,B_80)) = k2_pre_topc(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_271,plain,(
    ! [A_104,B_105] :
      ( k2_pre_topc(A_104,k2_pre_topc(A_104,k1_tops_1(A_104,B_105))) = k2_pre_topc(A_104,k1_tops_1(A_104,B_105))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_277,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_271])).

tff(c_282,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_188,c_188,c_277])).

tff(c_200,plain,(
    ! [A_93,B_94] :
      ( k4_subset_1(u1_struct_0(A_93),B_94,k2_tops_1(A_93,B_94)) = k2_pre_topc(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_206,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_200])).

tff(c_211,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_206])).

tff(c_283,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_211])).

tff(c_30,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k2_tops_1(A_45,B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_subset_1(A_81,B_82,C_83) = k2_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [B_84] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_84,'#skF_2') = k2_xboole_0(B_84,'#skF_2')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_132,plain,(
    ! [B_46] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_46),'#skF_2') = k2_xboole_0(k2_tops_1('#skF_1',B_46),'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_225,plain,(
    ! [B_102] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_102),'#skF_2') = k2_xboole_0(k2_tops_1('#skF_1',B_102),'#skF_2')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_132])).

tff(c_243,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_225])).

tff(c_147,plain,(
    ! [A_85,C_86,B_87] :
      ( k4_subset_1(A_85,C_86,B_87) = k4_subset_1(A_85,B_87,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [B_88] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_88,'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_147])).

tff(c_165,plain,(
    ! [B_46] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_46),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_346,plain,(
    ! [B_111] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_111),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_111))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_165])).

tff(c_357,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_346])).

tff(c_365,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_243,c_357])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_370,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_2])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.34  
% 2.75/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.34  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.75/1.34  
% 2.75/1.34  %Foreground sorts:
% 2.75/1.34  
% 2.75/1.34  
% 2.75/1.34  %Background operators:
% 2.75/1.34  
% 2.75/1.34  
% 2.75/1.34  %Foreground operators:
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.75/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.75/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.75/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.75/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.75/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.34  
% 2.75/1.36  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 2.75/1.36  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.75/1.36  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.75/1.36  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.75/1.36  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 2.75/1.36  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.75/1.36  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.75/1.36  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.75/1.36  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.75/1.36  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.75/1.36  tff(c_36, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.75/1.36  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.75/1.36  tff(c_177, plain, (![A_89, B_90]: (k2_pre_topc(A_89, k1_tops_1(A_89, B_90))=B_90 | ~v5_tops_1(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.75/1.36  tff(c_183, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_177])).
% 2.75/1.36  tff(c_188, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_183])).
% 2.75/1.36  tff(c_34, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.75/1.36  tff(c_189, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_34])).
% 2.75/1.36  tff(c_28, plain, (![A_43, B_44]: (m1_subset_1(k1_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.75/1.36  tff(c_98, plain, (![A_79, B_80]: (k2_pre_topc(A_79, k2_pre_topc(A_79, B_80))=k2_pre_topc(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.75/1.36  tff(c_271, plain, (![A_104, B_105]: (k2_pre_topc(A_104, k2_pre_topc(A_104, k1_tops_1(A_104, B_105)))=k2_pre_topc(A_104, k1_tops_1(A_104, B_105)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_28, c_98])).
% 2.75/1.36  tff(c_277, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_271])).
% 2.75/1.36  tff(c_282, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_188, c_188, c_277])).
% 2.75/1.36  tff(c_200, plain, (![A_93, B_94]: (k4_subset_1(u1_struct_0(A_93), B_94, k2_tops_1(A_93, B_94))=k2_pre_topc(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.36  tff(c_206, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_200])).
% 2.75/1.36  tff(c_211, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_206])).
% 2.75/1.36  tff(c_283, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_211])).
% 2.75/1.36  tff(c_30, plain, (![A_45, B_46]: (m1_subset_1(k2_tops_1(A_45, B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.36  tff(c_114, plain, (![A_81, B_82, C_83]: (k4_subset_1(A_81, B_82, C_83)=k2_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.36  tff(c_124, plain, (![B_84]: (k4_subset_1(u1_struct_0('#skF_1'), B_84, '#skF_2')=k2_xboole_0(B_84, '#skF_2') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_38, c_114])).
% 2.75/1.36  tff(c_132, plain, (![B_46]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_46), '#skF_2')=k2_xboole_0(k2_tops_1('#skF_1', B_46), '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_124])).
% 2.75/1.36  tff(c_225, plain, (![B_102]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_102), '#skF_2')=k2_xboole_0(k2_tops_1('#skF_1', B_102), '#skF_2') | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_132])).
% 2.75/1.36  tff(c_243, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_225])).
% 2.75/1.36  tff(c_147, plain, (![A_85, C_86, B_87]: (k4_subset_1(A_85, C_86, B_87)=k4_subset_1(A_85, B_87, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_85)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.36  tff(c_157, plain, (![B_88]: (k4_subset_1(u1_struct_0('#skF_1'), B_88, '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_38, c_147])).
% 2.75/1.36  tff(c_165, plain, (![B_46]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_46), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_157])).
% 2.75/1.36  tff(c_346, plain, (![B_111]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_111), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_111)) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_165])).
% 2.75/1.36  tff(c_357, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_346])).
% 2.75/1.36  tff(c_365, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_243, c_357])).
% 2.75/1.36  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.36  tff(c_370, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_365, c_2])).
% 2.75/1.36  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_370])).
% 2.75/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.36  
% 2.75/1.36  Inference rules
% 2.75/1.36  ----------------------
% 2.75/1.36  #Ref     : 0
% 2.75/1.36  #Sup     : 80
% 2.75/1.36  #Fact    : 0
% 2.75/1.36  #Define  : 0
% 2.75/1.36  #Split   : 1
% 2.75/1.36  #Chain   : 0
% 2.75/1.36  #Close   : 0
% 2.75/1.36  
% 2.75/1.36  Ordering : KBO
% 2.75/1.36  
% 2.75/1.36  Simplification rules
% 2.75/1.36  ----------------------
% 2.75/1.36  #Subsume      : 0
% 2.75/1.36  #Demod        : 33
% 2.75/1.36  #Tautology    : 38
% 2.75/1.36  #SimpNegUnit  : 1
% 2.75/1.36  #BackRed      : 3
% 2.75/1.36  
% 2.75/1.36  #Partial instantiations: 0
% 2.75/1.36  #Strategies tried      : 1
% 2.75/1.36  
% 2.75/1.36  Timing (in seconds)
% 2.75/1.36  ----------------------
% 2.89/1.36  Preprocessing        : 0.34
% 2.89/1.36  Parsing              : 0.18
% 2.89/1.36  CNF conversion       : 0.02
% 2.89/1.36  Main loop            : 0.25
% 2.89/1.36  Inferencing          : 0.09
% 2.89/1.36  Reduction            : 0.08
% 2.89/1.36  Demodulation         : 0.06
% 2.89/1.37  BG Simplification    : 0.02
% 2.89/1.37  Subsumption          : 0.05
% 2.89/1.37  Abstraction          : 0.02
% 2.89/1.37  MUC search           : 0.00
% 2.89/1.37  Cooper               : 0.00
% 2.89/1.37  Total                : 0.63
% 2.89/1.37  Index Insertion      : 0.00
% 2.89/1.37  Index Deletion       : 0.00
% 2.89/1.37  Index Matching       : 0.00
% 2.89/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
