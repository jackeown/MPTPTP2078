%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:15 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 153 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 293 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1604,plain,(
    ! [A_123,B_124] :
      ( k2_pre_topc(A_123,k1_tops_1(A_123,B_124)) = B_124
      | ~ v5_tops_1(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1608,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1604])).

tff(c_1612,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1608])).

tff(c_40,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1613,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_40])).

tff(c_580,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_subset_1(A_96,B_97,C_98) = k4_xboole_0(B_97,C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_583,plain,(
    ! [C_98] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_98) = k4_xboole_0('#skF_2',C_98) ),
    inference(resolution,[status(thm)],[c_44,c_580])).

tff(c_34,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k1_tops_1(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2558,plain,(
    ! [A_142,B_143] :
      ( k7_subset_1(u1_struct_0(A_142),k2_pre_topc(A_142,B_143),k1_tops_1(A_142,B_143)) = k2_tops_1(A_142,B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2567,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_2558])).

tff(c_2574,plain,
    ( k4_xboole_0('#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_583,c_2567])).

tff(c_3345,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2574])).

tff(c_3348,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3345])).

tff(c_3352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3348])).

tff(c_3354,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2574])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( k2_pre_topc(A_43,k2_pre_topc(A_43,B_44)) = k2_pre_topc(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3358,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3354,c_28])).

tff(c_3368,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1612,c_1612,c_3358])).

tff(c_36,plain,(
    ! [A_50,B_52] :
      ( k7_subset_1(u1_struct_0(A_50),k2_pre_topc(A_50,B_52),k1_tops_1(A_50,B_52)) = k2_tops_1(A_50,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3377,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3368,c_36])).

tff(c_3381,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_583,c_3377])).

tff(c_907,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_tops_1(A_106,B_107),B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_909,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_907])).

tff(c_912,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_909])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_916,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_912,c_6])).

tff(c_124,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_60,B_59] : r1_tarski(A_60,k2_xboole_0(B_59,A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_130,plain,(
    ! [B_70,A_69] : r1_tarski(k4_xboole_0(B_70,A_69),k2_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_63])).

tff(c_953,plain,(
    r1_tarski(k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_130])).

tff(c_3387,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3381,c_953])).

tff(c_3389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1613,c_3387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.83  
% 4.37/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.84  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.37/1.84  
% 4.37/1.84  %Foreground sorts:
% 4.37/1.84  
% 4.37/1.84  
% 4.37/1.84  %Background operators:
% 4.37/1.84  
% 4.37/1.84  
% 4.37/1.84  %Foreground operators:
% 4.37/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.84  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.37/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.37/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.37/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.37/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.37/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.84  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.37/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.84  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 4.37/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.37/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.37/1.84  
% 4.37/1.85  tff(f_100, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 4.37/1.85  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 4.37/1.85  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.37/1.85  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.37/1.85  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.37/1.85  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 4.37/1.85  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.37/1.85  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.37/1.85  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.37/1.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.37/1.85  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.37/1.85  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/1.85  tff(c_42, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/1.85  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/1.85  tff(c_1604, plain, (![A_123, B_124]: (k2_pre_topc(A_123, k1_tops_1(A_123, B_124))=B_124 | ~v5_tops_1(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.85  tff(c_1608, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1604])).
% 4.37/1.85  tff(c_1612, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1608])).
% 4.37/1.85  tff(c_40, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/1.85  tff(c_1613, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_40])).
% 4.37/1.85  tff(c_580, plain, (![A_96, B_97, C_98]: (k7_subset_1(A_96, B_97, C_98)=k4_xboole_0(B_97, C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.37/1.85  tff(c_583, plain, (![C_98]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_98)=k4_xboole_0('#skF_2', C_98))), inference(resolution, [status(thm)], [c_44, c_580])).
% 4.37/1.85  tff(c_34, plain, (![A_48, B_49]: (m1_subset_1(k1_tops_1(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.37/1.85  tff(c_2558, plain, (![A_142, B_143]: (k7_subset_1(u1_struct_0(A_142), k2_pre_topc(A_142, B_143), k1_tops_1(A_142, B_143))=k2_tops_1(A_142, B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.37/1.85  tff(c_2567, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1612, c_2558])).
% 4.37/1.85  tff(c_2574, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_583, c_2567])).
% 4.37/1.85  tff(c_3345, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2574])).
% 4.37/1.85  tff(c_3348, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3345])).
% 4.37/1.85  tff(c_3352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3348])).
% 4.37/1.85  tff(c_3354, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2574])).
% 4.37/1.85  tff(c_28, plain, (![A_43, B_44]: (k2_pre_topc(A_43, k2_pre_topc(A_43, B_44))=k2_pre_topc(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.37/1.85  tff(c_3358, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3354, c_28])).
% 4.37/1.85  tff(c_3368, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1612, c_1612, c_3358])).
% 4.37/1.85  tff(c_36, plain, (![A_50, B_52]: (k7_subset_1(u1_struct_0(A_50), k2_pre_topc(A_50, B_52), k1_tops_1(A_50, B_52))=k2_tops_1(A_50, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.37/1.85  tff(c_3377, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3368, c_36])).
% 4.37/1.85  tff(c_3381, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_583, c_3377])).
% 4.37/1.85  tff(c_907, plain, (![A_106, B_107]: (r1_tarski(k1_tops_1(A_106, B_107), B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.37/1.85  tff(c_909, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_907])).
% 4.37/1.85  tff(c_912, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_909])).
% 4.37/1.85  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.85  tff(c_916, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_912, c_6])).
% 4.37/1.85  tff(c_124, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/1.85  tff(c_48, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.85  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.85  tff(c_63, plain, (![A_60, B_59]: (r1_tarski(A_60, k2_xboole_0(B_59, A_60)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 4.37/1.85  tff(c_130, plain, (![B_70, A_69]: (r1_tarski(k4_xboole_0(B_70, A_69), k2_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_63])).
% 4.37/1.85  tff(c_953, plain, (r1_tarski(k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_916, c_130])).
% 4.37/1.85  tff(c_3387, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3381, c_953])).
% 4.37/1.85  tff(c_3389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1613, c_3387])).
% 4.37/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.85  
% 4.37/1.85  Inference rules
% 4.37/1.85  ----------------------
% 4.37/1.85  #Ref     : 0
% 4.37/1.85  #Sup     : 853
% 4.37/1.85  #Fact    : 0
% 4.37/1.85  #Define  : 0
% 4.37/1.85  #Split   : 1
% 4.37/1.85  #Chain   : 0
% 4.37/1.85  #Close   : 0
% 4.37/1.85  
% 4.37/1.85  Ordering : KBO
% 4.37/1.85  
% 4.37/1.85  Simplification rules
% 4.37/1.85  ----------------------
% 4.37/1.85  #Subsume      : 14
% 4.37/1.85  #Demod        : 1225
% 4.37/1.85  #Tautology    : 582
% 4.37/1.85  #SimpNegUnit  : 1
% 4.37/1.85  #BackRed      : 6
% 4.37/1.85  
% 4.37/1.85  #Partial instantiations: 0
% 4.37/1.85  #Strategies tried      : 1
% 4.37/1.85  
% 4.37/1.85  Timing (in seconds)
% 4.37/1.85  ----------------------
% 4.37/1.85  Preprocessing        : 0.33
% 4.37/1.85  Parsing              : 0.18
% 4.37/1.85  CNF conversion       : 0.02
% 4.37/1.85  Main loop            : 0.71
% 4.37/1.85  Inferencing          : 0.19
% 4.37/1.85  Reduction            : 0.36
% 4.37/1.85  Demodulation         : 0.30
% 4.37/1.85  BG Simplification    : 0.03
% 4.37/1.85  Subsumption          : 0.10
% 4.37/1.85  Abstraction          : 0.03
% 4.37/1.85  MUC search           : 0.00
% 4.37/1.85  Cooper               : 0.00
% 4.37/1.85  Total                : 1.08
% 4.37/1.85  Index Insertion      : 0.00
% 4.37/1.85  Index Deletion       : 0.00
% 4.37/1.85  Index Matching       : 0.00
% 4.37/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
