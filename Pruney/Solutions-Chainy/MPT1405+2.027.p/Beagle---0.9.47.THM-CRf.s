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
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 175 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 388 expanded)
%              Number of equality atoms :    9 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_22,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_48,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_39,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_49,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103,plain,(
    ! [A_33] : r1_tarski(A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_tops_1(A_11,k2_struct_0(A_11)) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_228,plain,(
    ! [C_50,A_51,B_52] :
      ( m2_connsp_2(C_50,A_51,B_52)
      | ~ r1_tarski(B_52,k1_tops_1(A_51,C_50))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_643,plain,(
    ! [C_75,A_76] :
      ( m2_connsp_2(C_75,A_76,k1_tops_1(A_76,C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(k1_tops_1(A_76,C_75),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_103,c_228])).

tff(c_650,plain,(
    ! [C_75] :
      ( m2_connsp_2(C_75,'#skF_1',k1_tops_1('#skF_1',C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1',C_75),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_643])).

tff(c_654,plain,(
    ! [C_77] :
      ( m2_connsp_2(C_77,'#skF_1',k1_tops_1('#skF_1',C_77))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1',C_77),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_48,c_650])).

tff(c_657,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',k1_tops_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_654])).

tff(c_662,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',k1_tops_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_657])).

tff(c_664,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_667,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_664])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_667])).

tff(c_673,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_943,plain,(
    ! [A_88,B_89] :
      ( m2_connsp_2(k2_struct_0(A_88),A_88,B_89)
      | ~ r1_tarski(B_89,k2_struct_0(A_88))
      | ~ m1_subset_1(k2_struct_0(A_88),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_948,plain,(
    ! [B_89] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_89)
      | ~ r1_tarski(B_89,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_943])).

tff(c_952,plain,(
    ! [B_90] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_90)
      | ~ r1_tarski(B_90,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_28,c_26,c_48,c_673,c_948])).

tff(c_962,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_952])).

tff(c_969,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_962])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.59  
% 3.05/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.59  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.05/1.59  
% 3.05/1.59  %Foreground sorts:
% 3.05/1.59  
% 3.05/1.59  
% 3.05/1.59  %Background operators:
% 3.05/1.59  
% 3.05/1.59  
% 3.05/1.59  %Foreground operators:
% 3.05/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.05/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.05/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.05/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.05/1.59  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.05/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.59  
% 3.05/1.60  tff(f_78, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.05/1.60  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.05/1.60  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.05/1.60  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.60  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.05/1.60  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.05/1.60  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.05/1.60  tff(f_51, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.05/1.60  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.05/1.60  tff(c_22, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.60  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.60  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.05/1.60  tff(c_34, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.60  tff(c_44, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_14, c_34])).
% 3.05/1.60  tff(c_48, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_44])).
% 3.05/1.60  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.60  tff(c_39, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.60  tff(c_43, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_39])).
% 3.05/1.60  tff(c_49, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_43])).
% 3.05/1.60  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 3.05/1.60  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.60  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.60  tff(c_65, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.60  tff(c_97, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(resolution, [status(thm)], [c_6, c_65])).
% 3.05/1.60  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.60  tff(c_103, plain, (![A_33]: (r1_tarski(A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 3.05/1.60  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.60  tff(c_16, plain, (![A_11]: (k1_tops_1(A_11, k2_struct_0(A_11))=k2_struct_0(A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.05/1.60  tff(c_228, plain, (![C_50, A_51, B_52]: (m2_connsp_2(C_50, A_51, B_52) | ~r1_tarski(B_52, k1_tops_1(A_51, C_50)) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.05/1.60  tff(c_643, plain, (![C_75, A_76]: (m2_connsp_2(C_75, A_76, k1_tops_1(A_76, C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(k1_tops_1(A_76, C_75), k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(resolution, [status(thm)], [c_103, c_228])).
% 3.05/1.60  tff(c_650, plain, (![C_75]: (m2_connsp_2(C_75, '#skF_1', k1_tops_1('#skF_1', C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', C_75), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_643])).
% 3.05/1.60  tff(c_654, plain, (![C_77]: (m2_connsp_2(C_77, '#skF_1', k1_tops_1('#skF_1', C_77)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', C_77), k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_48, c_650])).
% 3.05/1.60  tff(c_657, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', k1_tops_1('#skF_1', k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_654])).
% 3.05/1.60  tff(c_662, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', k1_tops_1('#skF_1', k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_657])).
% 3.05/1.60  tff(c_664, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_662])).
% 3.05/1.60  tff(c_667, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_664])).
% 3.05/1.60  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_667])).
% 3.05/1.60  tff(c_673, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_662])).
% 3.05/1.60  tff(c_943, plain, (![A_88, B_89]: (m2_connsp_2(k2_struct_0(A_88), A_88, B_89) | ~r1_tarski(B_89, k2_struct_0(A_88)) | ~m1_subset_1(k2_struct_0(A_88), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(superposition, [status(thm), theory('equality')], [c_16, c_228])).
% 3.05/1.60  tff(c_948, plain, (![B_89]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_89) | ~r1_tarski(B_89, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_943])).
% 3.05/1.60  tff(c_952, plain, (![B_90]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_90) | ~r1_tarski(B_90, k2_struct_0('#skF_1')) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_28, c_26, c_48, c_673, c_948])).
% 3.05/1.60  tff(c_962, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_952])).
% 3.05/1.60  tff(c_969, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_962])).
% 3.05/1.60  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_969])).
% 3.05/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.60  
% 3.05/1.60  Inference rules
% 3.05/1.60  ----------------------
% 3.05/1.60  #Ref     : 0
% 3.05/1.60  #Sup     : 204
% 3.05/1.60  #Fact    : 0
% 3.05/1.60  #Define  : 0
% 3.05/1.60  #Split   : 4
% 3.05/1.60  #Chain   : 0
% 3.05/1.60  #Close   : 0
% 3.05/1.60  
% 3.05/1.60  Ordering : KBO
% 3.05/1.60  
% 3.05/1.60  Simplification rules
% 3.05/1.60  ----------------------
% 3.05/1.60  #Subsume      : 38
% 3.05/1.60  #Demod        : 202
% 3.05/1.60  #Tautology    : 86
% 3.05/1.60  #SimpNegUnit  : 1
% 3.05/1.60  #BackRed      : 2
% 3.05/1.60  
% 3.05/1.60  #Partial instantiations: 0
% 3.05/1.60  #Strategies tried      : 1
% 3.05/1.60  
% 3.05/1.60  Timing (in seconds)
% 3.05/1.60  ----------------------
% 3.05/1.61  Preprocessing        : 0.41
% 3.05/1.61  Parsing              : 0.21
% 3.05/1.61  CNF conversion       : 0.02
% 3.05/1.61  Main loop            : 0.41
% 3.05/1.61  Inferencing          : 0.15
% 3.05/1.61  Reduction            : 0.14
% 3.05/1.61  Demodulation         : 0.10
% 3.05/1.61  BG Simplification    : 0.02
% 3.05/1.61  Subsumption          : 0.08
% 3.05/1.61  Abstraction          : 0.02
% 3.05/1.61  MUC search           : 0.00
% 3.05/1.61  Cooper               : 0.00
% 3.05/1.61  Total                : 0.84
% 3.05/1.61  Index Insertion      : 0.00
% 3.05/1.61  Index Deletion       : 0.00
% 3.05/1.61  Index Matching       : 0.00
% 3.05/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
