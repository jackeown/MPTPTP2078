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
% DateTime   : Thu Dec  3 10:22:18 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 203 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 485 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_pre_topc(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(u1_struct_0(A_49),k2_pre_topc(A_49,k3_subset_1(u1_struct_0(A_49),B_50))) = k1_tops_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_225,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k1_tops_1(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(k2_pre_topc(A_64,k3_subset_1(u1_struct_0(A_64),B_65)),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2])).

tff(c_234,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k1_tops_1(A_66,B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_66),B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_225])).

tff(c_243,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k1_tops_1(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68))) ) ),
    inference(resolution,[status(thm)],[c_2,c_234])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [A_38,B_39] :
      ( k2_tops_1(A_38,k1_tops_1(A_38,B_39)) = k2_tops_1(A_38,B_39)
      | ~ v5_tops_1(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_75,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_81,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_75])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_85,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_20])).

tff(c_89,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_91,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_254,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_243,c_91])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_254])).

tff(c_268,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( k2_pre_topc(A_34,k1_tops_1(A_34,B_35)) = B_35
      | ~ v5_tops_1(B_35,A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_43,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_49,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_43])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_267,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_336,plain,(
    ! [A_84,B_85] :
      ( k9_subset_1(u1_struct_0(A_84),k2_pre_topc(A_84,B_85),k2_pre_topc(A_84,k3_subset_1(u1_struct_0(A_84),B_85))) = k2_tops_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_353,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_336])).

tff(c_357,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_268,c_81,c_353])).

tff(c_8,plain,(
    ! [A_7,B_8,C_10] :
      ( r1_tarski(k3_subset_1(A_7,B_8),k3_subset_1(A_7,k9_subset_1(A_7,B_8,C_10)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_293,plain,(
    ! [B_76,C_77,A_78] :
      ( r1_tarski(B_76,C_77)
      | ~ r1_tarski(k3_subset_1(A_78,C_77),k3_subset_1(A_78,B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_300,plain,(
    ! [A_7,B_8,C_10] :
      ( r1_tarski(k9_subset_1(A_7,B_8,C_10),B_8)
      | ~ m1_subset_1(k9_subset_1(A_7,B_8,C_10),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_8,c_293])).

tff(c_360,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_300])).

tff(c_367,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_267,c_357,c_360])).

tff(c_368,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_367])).

tff(c_374,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_368])).

tff(c_377,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_374])).

tff(c_380,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_377])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:37:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.43/1.38  
% 2.43/1.38  %Foreground sorts:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Background operators:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Foreground operators:
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.38  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.43/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.43/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.43/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.38  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.43/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.43/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.38  
% 2.72/1.40  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 2.72/1.40  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.72/1.40  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.72/1.40  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.72/1.40  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 2.72/1.40  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.72/1.40  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.72/1.40  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 2.72/1.40  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 2.72/1.40  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.72/1.40  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.40  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.40  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.40  tff(c_10, plain, (![A_11, B_12]: (m1_subset_1(k2_pre_topc(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.40  tff(c_103, plain, (![A_49, B_50]: (k3_subset_1(u1_struct_0(A_49), k2_pre_topc(A_49, k3_subset_1(u1_struct_0(A_49), B_50)))=k1_tops_1(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.40  tff(c_225, plain, (![A_64, B_65]: (m1_subset_1(k1_tops_1(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(k2_pre_topc(A_64, k3_subset_1(u1_struct_0(A_64), B_65)), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2])).
% 2.72/1.40  tff(c_234, plain, (![A_66, B_67]: (m1_subset_1(k1_tops_1(A_66, B_67), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_66), B_67), k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_10, c_225])).
% 2.72/1.40  tff(c_243, plain, (![A_68, B_69]: (m1_subset_1(k1_tops_1(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))))), inference(resolution, [status(thm)], [c_2, c_234])).
% 2.72/1.40  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.40  tff(c_66, plain, (![A_38, B_39]: (k2_tops_1(A_38, k1_tops_1(A_38, B_39))=k2_tops_1(A_38, B_39) | ~v5_tops_1(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.40  tff(c_75, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.72/1.40  tff(c_81, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_75])).
% 2.72/1.40  tff(c_20, plain, (![A_22, B_23]: (m1_subset_1(k2_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.72/1.40  tff(c_85, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81, c_20])).
% 2.72/1.40  tff(c_89, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_85])).
% 2.72/1.40  tff(c_91, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_89])).
% 2.72/1.40  tff(c_254, plain, (~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_243, c_91])).
% 2.72/1.40  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_254])).
% 2.72/1.40  tff(c_268, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_89])).
% 2.72/1.40  tff(c_34, plain, (![A_34, B_35]: (k2_pre_topc(A_34, k1_tops_1(A_34, B_35))=B_35 | ~v5_tops_1(B_35, A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.40  tff(c_43, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.72/1.40  tff(c_49, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_43])).
% 2.72/1.40  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.40  tff(c_50, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_24])).
% 2.72/1.40  tff(c_267, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_89])).
% 2.72/1.40  tff(c_336, plain, (![A_84, B_85]: (k9_subset_1(u1_struct_0(A_84), k2_pre_topc(A_84, B_85), k2_pre_topc(A_84, k3_subset_1(u1_struct_0(A_84), B_85)))=k2_tops_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.72/1.40  tff(c_353, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_336])).
% 2.72/1.40  tff(c_357, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_268, c_81, c_353])).
% 2.72/1.40  tff(c_8, plain, (![A_7, B_8, C_10]: (r1_tarski(k3_subset_1(A_7, B_8), k3_subset_1(A_7, k9_subset_1(A_7, B_8, C_10))) | ~m1_subset_1(C_10, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.40  tff(c_293, plain, (![B_76, C_77, A_78]: (r1_tarski(B_76, C_77) | ~r1_tarski(k3_subset_1(A_78, C_77), k3_subset_1(A_78, B_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.40  tff(c_300, plain, (![A_7, B_8, C_10]: (r1_tarski(k9_subset_1(A_7, B_8, C_10), B_8) | ~m1_subset_1(k9_subset_1(A_7, B_8, C_10), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_8, c_293])).
% 2.72/1.40  tff(c_360, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')))), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_357, c_300])).
% 2.72/1.40  tff(c_367, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_267, c_357, c_360])).
% 2.72/1.40  tff(c_368, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_367])).
% 2.72/1.40  tff(c_374, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_368])).
% 2.72/1.40  tff(c_377, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_374])).
% 2.72/1.40  tff(c_380, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_377])).
% 2.72/1.40  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_380])).
% 2.72/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  Inference rules
% 2.72/1.40  ----------------------
% 2.72/1.40  #Ref     : 0
% 2.72/1.40  #Sup     : 88
% 2.72/1.40  #Fact    : 0
% 2.72/1.40  #Define  : 0
% 2.72/1.40  #Split   : 5
% 2.72/1.40  #Chain   : 0
% 2.72/1.40  #Close   : 0
% 2.72/1.40  
% 2.72/1.40  Ordering : KBO
% 2.72/1.40  
% 2.72/1.40  Simplification rules
% 2.72/1.40  ----------------------
% 2.72/1.40  #Subsume      : 7
% 2.72/1.40  #Demod        : 33
% 2.72/1.40  #Tautology    : 18
% 2.72/1.40  #SimpNegUnit  : 1
% 2.72/1.40  #BackRed      : 1
% 2.72/1.40  
% 2.72/1.40  #Partial instantiations: 0
% 2.72/1.40  #Strategies tried      : 1
% 2.72/1.40  
% 2.72/1.40  Timing (in seconds)
% 2.72/1.40  ----------------------
% 2.72/1.40  Preprocessing        : 0.31
% 2.72/1.40  Parsing              : 0.18
% 2.72/1.40  CNF conversion       : 0.02
% 2.72/1.40  Main loop            : 0.28
% 2.72/1.40  Inferencing          : 0.10
% 2.72/1.40  Reduction            : 0.08
% 2.72/1.40  Demodulation         : 0.06
% 2.72/1.40  BG Simplification    : 0.02
% 2.72/1.40  Subsumption          : 0.06
% 2.72/1.40  Abstraction          : 0.02
% 2.72/1.40  MUC search           : 0.00
% 2.72/1.40  Cooper               : 0.00
% 2.72/1.40  Total                : 0.63
% 2.72/1.40  Index Insertion      : 0.00
% 2.72/1.40  Index Deletion       : 0.00
% 2.72/1.40  Index Matching       : 0.00
% 2.72/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
