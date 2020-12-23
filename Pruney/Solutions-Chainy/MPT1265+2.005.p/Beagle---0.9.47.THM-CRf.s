%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:42 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 214 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    ! [A_29,B_30,C_31] :
      ( k9_subset_1(A_29,B_30,C_31) = k3_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [B_30] : k9_subset_1(u1_struct_0('#skF_1'),B_30,'#skF_2') = k3_xboole_0(B_30,'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_286,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = k2_struct_0(A_49)
      | ~ v1_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_314,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_286])).

tff(c_339,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20,c_314])).

tff(c_506,plain,(
    ! [A_61,C_62,B_63] :
      ( k2_pre_topc(A_61,k9_subset_1(u1_struct_0(A_61),C_62,B_63)) = k2_pre_topc(A_61,C_62)
      | ~ v3_pre_topc(C_62,A_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ v1_tops_1(B_63,A_61)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_533,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_63)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_506])).

tff(c_614,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_66)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_18,c_339,c_533])).

tff(c_654,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_614])).

tff(c_674,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78,c_654])).

tff(c_100,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k9_subset_1(A_34,B_35,C_36),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [B_30] :
      ( m1_subset_1(k3_xboole_0(B_30,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_100])).

tff(c_150,plain,(
    ! [B_40] : m1_subset_1(k3_xboole_0(B_40,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_10,plain,(
    ! [B_13,A_11] :
      ( v1_tops_1(B_13,A_11)
      | k2_pre_topc(A_11,B_13) != k2_struct_0(A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,(
    ! [B_40] :
      ( v1_tops_1(k3_xboole_0(B_40,'#skF_2'),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(B_40,'#skF_2')) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_840,plain,(
    ! [B_79] :
      ( v1_tops_1(k3_xboole_0(B_79,'#skF_2'),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(B_79,'#skF_2')) != k2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [B_30] : k9_subset_1(u1_struct_0('#skF_1'),B_30,'#skF_3') = k3_xboole_0(B_30,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_16,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_89,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_90,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_846,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_840,c_90])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:33:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.52  
% 2.91/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.52  %$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.91/1.52  
% 2.91/1.52  %Foreground sorts:
% 2.91/1.52  
% 2.91/1.52  
% 2.91/1.52  %Background operators:
% 2.91/1.52  
% 2.91/1.52  
% 2.91/1.52  %Foreground operators:
% 2.91/1.52  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.91/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.91/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.52  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.91/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.91/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.91/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.91/1.52  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.91/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.91/1.52  
% 3.00/1.53  tff(f_81, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 3.00/1.53  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.00/1.53  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.00/1.53  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 3.00/1.53  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.00/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.53  tff(c_22, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_73, plain, (![A_29, B_30, C_31]: (k9_subset_1(A_29, B_30, C_31)=k3_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.53  tff(c_78, plain, (![B_30]: (k9_subset_1(u1_struct_0('#skF_1'), B_30, '#skF_2')=k3_xboole_0(B_30, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_73])).
% 3.00/1.53  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_18, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_20, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_286, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=k2_struct_0(A_49) | ~v1_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.00/1.53  tff(c_314, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_286])).
% 3.00/1.53  tff(c_339, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20, c_314])).
% 3.00/1.53  tff(c_506, plain, (![A_61, C_62, B_63]: (k2_pre_topc(A_61, k9_subset_1(u1_struct_0(A_61), C_62, B_63))=k2_pre_topc(A_61, C_62) | ~v3_pre_topc(C_62, A_61) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~v1_tops_1(B_63, A_61) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.53  tff(c_533, plain, (![B_63]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_63))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_506])).
% 3.00/1.53  tff(c_614, plain, (![B_66]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_66))=k2_struct_0('#skF_1') | ~v1_tops_1(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_18, c_339, c_533])).
% 3.00/1.53  tff(c_654, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_614])).
% 3.00/1.53  tff(c_674, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_78, c_654])).
% 3.00/1.53  tff(c_100, plain, (![A_34, B_35, C_36]: (m1_subset_1(k9_subset_1(A_34, B_35, C_36), k1_zfmisc_1(A_34)) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.53  tff(c_108, plain, (![B_30]: (m1_subset_1(k3_xboole_0(B_30, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_100])).
% 3.00/1.53  tff(c_150, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_108])).
% 3.00/1.53  tff(c_10, plain, (![B_13, A_11]: (v1_tops_1(B_13, A_11) | k2_pre_topc(A_11, B_13)!=k2_struct_0(A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.00/1.53  tff(c_153, plain, (![B_40]: (v1_tops_1(k3_xboole_0(B_40, '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(B_40, '#skF_2'))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_150, c_10])).
% 3.00/1.53  tff(c_840, plain, (![B_79]: (v1_tops_1(k3_xboole_0(B_79, '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(B_79, '#skF_2'))!=k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153])).
% 3.00/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.53  tff(c_79, plain, (![B_30]: (k9_subset_1(u1_struct_0('#skF_1'), B_30, '#skF_3')=k3_xboole_0(B_30, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_73])).
% 3.00/1.53  tff(c_16, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.53  tff(c_89, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_16])).
% 3.00/1.53  tff(c_90, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_89])).
% 3.00/1.53  tff(c_846, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_840, c_90])).
% 3.00/1.53  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_846])).
% 3.00/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.53  
% 3.00/1.53  Inference rules
% 3.00/1.53  ----------------------
% 3.00/1.53  #Ref     : 0
% 3.00/1.53  #Sup     : 179
% 3.00/1.53  #Fact    : 0
% 3.00/1.53  #Define  : 0
% 3.00/1.54  #Split   : 1
% 3.00/1.54  #Chain   : 0
% 3.00/1.54  #Close   : 0
% 3.00/1.54  
% 3.00/1.54  Ordering : KBO
% 3.00/1.54  
% 3.00/1.54  Simplification rules
% 3.00/1.54  ----------------------
% 3.00/1.54  #Subsume      : 2
% 3.00/1.54  #Demod        : 130
% 3.00/1.54  #Tautology    : 64
% 3.00/1.54  #SimpNegUnit  : 0
% 3.00/1.54  #BackRed      : 1
% 3.00/1.54  
% 3.00/1.54  #Partial instantiations: 0
% 3.00/1.54  #Strategies tried      : 1
% 3.00/1.54  
% 3.00/1.54  Timing (in seconds)
% 3.00/1.54  ----------------------
% 3.00/1.54  Preprocessing        : 0.33
% 3.00/1.54  Parsing              : 0.18
% 3.00/1.54  CNF conversion       : 0.02
% 3.00/1.54  Main loop            : 0.38
% 3.00/1.54  Inferencing          : 0.12
% 3.00/1.54  Reduction            : 0.16
% 3.00/1.54  Demodulation         : 0.13
% 3.00/1.54  BG Simplification    : 0.02
% 3.00/1.54  Subsumption          : 0.06
% 3.00/1.54  Abstraction          : 0.02
% 3.00/1.54  MUC search           : 0.00
% 3.00/1.54  Cooper               : 0.00
% 3.00/1.54  Total                : 0.75
% 3.00/1.54  Index Insertion      : 0.00
% 3.00/1.54  Index Deletion       : 0.00
% 3.00/1.54  Index Matching       : 0.00
% 3.00/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
