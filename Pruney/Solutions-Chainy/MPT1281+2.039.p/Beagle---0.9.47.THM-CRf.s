%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:18 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 180 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 398 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_135,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k1_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tops_1(A_46,B_47),u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_135,c_8])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_378,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,k1_tops_1(A_74,B_75)) = B_75
      | ~ v5_tops_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_388,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_378])).

tff(c_394,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_388])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(B_43,k2_pre_topc(A_44,B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    ! [A_8,A_44] :
      ( r1_tarski(A_8,k2_pre_topc(A_44,A_8))
      | ~ l1_pre_topc(A_44)
      | ~ r1_tarski(A_8,u1_struct_0(A_44)) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_399,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_111])).

tff(c_403,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_399])).

tff(c_435,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_438,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_149,c_435])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_438])).

tff(c_443,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_395,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_24])).

tff(c_47,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_9,A_8] :
      ( k4_xboole_0(B_9,A_8) = k3_subset_1(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_451,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_443,c_58])).

tff(c_74,plain,(
    ! [A_36,B_37,C_38] :
      ( k7_subset_1(A_36,B_37,C_38) = k4_xboole_0(B_37,C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [C_38] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_38) = k4_xboole_0('#skF_2',C_38) ),
    inference(resolution,[status(thm)],[c_28,c_74])).

tff(c_444,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_188,plain,(
    ! [A_56,B_57] :
      ( k2_pre_topc(A_56,k2_pre_topc(A_56,B_57)) = k2_pre_topc(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_513,plain,(
    ! [A_82,A_83] :
      ( k2_pre_topc(A_82,k2_pre_topc(A_82,A_83)) = k2_pre_topc(A_82,A_83)
      | ~ l1_pre_topc(A_82)
      | ~ r1_tarski(A_83,u1_struct_0(A_82)) ) ),
    inference(resolution,[status(thm)],[c_10,c_188])).

tff(c_515,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_444,c_513])).

tff(c_527,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_394,c_394,c_515])).

tff(c_557,plain,(
    ! [A_84,B_85] :
      ( k7_subset_1(u1_struct_0(A_84),k2_pre_topc(A_84,B_85),k1_tops_1(A_84,B_85)) = k2_tops_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_566,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_557])).

tff(c_573,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_451,c_83,c_566])).

tff(c_41,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k3_subset_1(A_28,B_29),A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_608,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_45])).

tff(c_616,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_608])).

tff(c_638,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_616])).

tff(c_642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:26:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.45  
% 2.45/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.45  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.45/1.45  
% 2.45/1.45  %Foreground sorts:
% 2.45/1.45  
% 2.45/1.45  
% 2.45/1.45  %Background operators:
% 2.45/1.45  
% 2.45/1.45  
% 2.45/1.45  %Foreground operators:
% 2.45/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.45  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.45/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.45/1.45  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.45/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.45/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.45  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.45/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.45/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.45  
% 2.84/1.46  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 2.84/1.46  tff(f_69, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.84/1.46  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.46  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.84/1.46  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.84/1.46  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.84/1.46  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.84/1.46  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.84/1.46  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.84/1.46  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.84/1.46  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.46  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.46  tff(c_135, plain, (![A_46, B_47]: (m1_subset_1(k1_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.84/1.46  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.46  tff(c_149, plain, (![A_46, B_47]: (r1_tarski(k1_tops_1(A_46, B_47), u1_struct_0(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_135, c_8])).
% 2.84/1.46  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.46  tff(c_378, plain, (![A_74, B_75]: (k2_pre_topc(A_74, k1_tops_1(A_74, B_75))=B_75 | ~v5_tops_1(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.84/1.46  tff(c_388, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_378])).
% 2.84/1.46  tff(c_394, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_388])).
% 2.84/1.46  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.46  tff(c_101, plain, (![B_43, A_44]: (r1_tarski(B_43, k2_pre_topc(A_44, B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.46  tff(c_111, plain, (![A_8, A_44]: (r1_tarski(A_8, k2_pre_topc(A_44, A_8)) | ~l1_pre_topc(A_44) | ~r1_tarski(A_8, u1_struct_0(A_44)))), inference(resolution, [status(thm)], [c_10, c_101])).
% 2.84/1.46  tff(c_399, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_394, c_111])).
% 2.84/1.46  tff(c_403, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_399])).
% 2.84/1.46  tff(c_435, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_403])).
% 2.84/1.46  tff(c_438, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_149, c_435])).
% 2.84/1.46  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_438])).
% 2.84/1.46  tff(c_443, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_403])).
% 2.84/1.46  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.46  tff(c_395, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_24])).
% 2.84/1.46  tff(c_47, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k3_subset_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.46  tff(c_58, plain, (![B_9, A_8]: (k4_xboole_0(B_9, A_8)=k3_subset_1(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_10, c_47])).
% 2.84/1.46  tff(c_451, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_443, c_58])).
% 2.84/1.46  tff(c_74, plain, (![A_36, B_37, C_38]: (k7_subset_1(A_36, B_37, C_38)=k4_xboole_0(B_37, C_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.46  tff(c_83, plain, (![C_38]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_38)=k4_xboole_0('#skF_2', C_38))), inference(resolution, [status(thm)], [c_28, c_74])).
% 2.84/1.46  tff(c_444, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_403])).
% 2.84/1.46  tff(c_188, plain, (![A_56, B_57]: (k2_pre_topc(A_56, k2_pre_topc(A_56, B_57))=k2_pre_topc(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.46  tff(c_513, plain, (![A_82, A_83]: (k2_pre_topc(A_82, k2_pre_topc(A_82, A_83))=k2_pre_topc(A_82, A_83) | ~l1_pre_topc(A_82) | ~r1_tarski(A_83, u1_struct_0(A_82)))), inference(resolution, [status(thm)], [c_10, c_188])).
% 2.84/1.46  tff(c_515, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_444, c_513])).
% 2.84/1.46  tff(c_527, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_394, c_394, c_515])).
% 2.84/1.46  tff(c_557, plain, (![A_84, B_85]: (k7_subset_1(u1_struct_0(A_84), k2_pre_topc(A_84, B_85), k1_tops_1(A_84, B_85))=k2_tops_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.46  tff(c_566, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_527, c_557])).
% 2.84/1.46  tff(c_573, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_451, c_83, c_566])).
% 2.84/1.46  tff(c_41, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.46  tff(c_45, plain, (![A_28, B_29]: (r1_tarski(k3_subset_1(A_28, B_29), A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_41, c_8])).
% 2.84/1.46  tff(c_608, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_45])).
% 2.84/1.46  tff(c_616, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_395, c_608])).
% 2.84/1.46  tff(c_638, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_10, c_616])).
% 2.84/1.46  tff(c_642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_443, c_638])).
% 2.84/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.46  
% 2.84/1.46  Inference rules
% 2.84/1.46  ----------------------
% 2.84/1.46  #Ref     : 0
% 2.84/1.46  #Sup     : 145
% 2.84/1.46  #Fact    : 0
% 2.84/1.46  #Define  : 0
% 2.84/1.46  #Split   : 3
% 2.84/1.46  #Chain   : 0
% 2.84/1.46  #Close   : 0
% 2.84/1.46  
% 2.84/1.46  Ordering : KBO
% 2.84/1.46  
% 2.84/1.46  Simplification rules
% 2.84/1.46  ----------------------
% 2.84/1.46  #Subsume      : 2
% 2.84/1.46  #Demod        : 91
% 2.84/1.46  #Tautology    : 74
% 2.84/1.46  #SimpNegUnit  : 1
% 2.84/1.46  #BackRed      : 15
% 2.84/1.46  
% 2.84/1.46  #Partial instantiations: 0
% 2.84/1.46  #Strategies tried      : 1
% 2.84/1.46  
% 2.84/1.46  Timing (in seconds)
% 2.84/1.46  ----------------------
% 2.84/1.47  Preprocessing        : 0.33
% 2.84/1.47  Parsing              : 0.17
% 2.84/1.47  CNF conversion       : 0.02
% 2.84/1.47  Main loop            : 0.33
% 2.84/1.47  Inferencing          : 0.13
% 2.84/1.47  Reduction            : 0.10
% 2.84/1.47  Demodulation         : 0.07
% 2.84/1.47  BG Simplification    : 0.02
% 2.84/1.47  Subsumption          : 0.06
% 2.84/1.47  Abstraction          : 0.02
% 2.84/1.47  MUC search           : 0.00
% 2.84/1.47  Cooper               : 0.00
% 2.84/1.47  Total                : 0.69
% 2.84/1.47  Index Insertion      : 0.00
% 2.84/1.47  Index Deletion       : 0.00
% 2.84/1.47  Index Matching       : 0.00
% 2.84/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
